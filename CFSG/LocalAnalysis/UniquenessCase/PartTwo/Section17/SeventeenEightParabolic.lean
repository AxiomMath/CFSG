module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33Parabolic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.GroupTheory.LiftPermutes
public import CFSG.GroupTheory.PermutesPullback
public import CFSG.GroupTheory.PermutingProducts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev innerT17_8 (D : Data G) (L : Subgroup G) : Subgroup G :=
  D.T ⊓ (L ⊔ pCoreOf 2 (L ⊔ D.T))

theorem le_normalizer_innerT17_8 {D : Data G} {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G)) :
    D.T ≤ normalizer (innerT17_8 D L : Set G) := by
  let H : Subgroup G := L ⊔ D.T
  have hTHnorm : D.T ≤ Subgroup.normalizer (H : Set G) := by
    refine (le_inf hTL Subgroup.le_normalizer).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_sup L D.T
  have hTO2 : D.T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hTHnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hTLO2 : D.T ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    refine (le_inf hTL hTO2).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_sup L (pCoreOf 2 H)
  have h2 : D.T ≤ Subgroup.normalizer ((D.T ⊓ (L ⊔ pCoreOf 2 H) : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hTLO2).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := D.T) (K := L ⊔ pCoreOf 2 H))
  simpa [innerT17_8, H] using h2

private theorem permutes_imageBar2 {H Y Z : Subgroup G} (hY : Y ≤ H) (hZ : Z ≤ H)
    (hperm : Permutes Y Z) :
    Permutes (S18.imageBar2 H Y) (S18.imageBar2 H Z) :=
  CFSG.GroupTheory.map_permutes_map (S18.piBar2 H)
    (CFSG.GroupTheory.permutes_of_map_permutes H.subtype (X := Y.subgroupOf H)
      (T := Z.subgroupOf H) (by rw [Subgroup.ker_subtype]; exact bot_le)
      (by rw [Subgroup.map_subgroupOf_eq_of_le hY, Subgroup.map_subgroupOf_eq_of_le hZ]
          exact hperm))

private theorem imageBar2_innerT17_8 {D : Data G} {L : Subgroup G} :
    S18.imageBar2 (L ⊔ D.T) (innerT17_8 D L) =
      S18.imageBar2 (L ⊔ D.T) D.T ⊓ S18.imageBar2 (L ⊔ D.T) L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := L ⊔ D.T
  have hLH : L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hTH
  have hO2H : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hO2image : S18.imageBar2 H (pCoreOf 2 H) = ⊥ := by
    show ((pCoreOf 2 H).subgroupOf H).map (S18.piBar2 H) = ⊥
    rw [Subgroup.map_eq_bot_iff]
    intro z hz
    exact (QuotientGroup.eq_one_iff z).mpr
      ((CFSG.mem_openPCoreOf_iff z).mp (Subgroup.mem_subgroupOf.mp hz))
  have himageL : S18.imageBar2 H (L ⊔ pCoreOf 2 H) = S18.imageBar2 H L := by
    rw [S18.imageBar2_sup hLH hO2H, hO2image, sup_bot_eq]
  rw [innerT17_8]
  change S18.imageBar2 H (D.T ⊓ (L ⊔ pCoreOf 2 H)) =
    S18.imageBar2 H D.T ⊓ S18.imageBar2 H L
  rw [← himageL, ← S18.imageBar2_inf_of_isSylowIn (H := H) (T := D.T)
    (K := L ⊔ pCoreOf 2 H) hTsyl]

private theorem ker_piBar2_le_innerT17_8 {D : Data G} {L : Subgroup G} :
    (S18.piBar2 (L ⊔ D.T)).ker ≤ (innerT17_8 D L).subgroupOf (L ⊔ D.T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := L ⊔ D.T
  have hTH : D.T ≤ H := le_sup_right
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hTH
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hxO2 : ((x : ↥H) : G) ∈ pCoreOf 2 H := by
    have h1 : (QuotientGroup.mk x : Bar2 H) = 1 := hx
    have h2 : x ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
    rw [← CFSG.openPCoreOf_subgroupOf 2 H] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  exact ⟨CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTsyl hxO2,
    Subgroup.mem_sup_right hxO2⟩

theorem mem_sup_pCoreOf_of_mem_imageBar2 {D : Data G} {L : Subgroup G} {x : G}
    (hxH : x ∈ L ⊔ D.T)
    (hxL : S18.piBar2 (L ⊔ D.T) ⟨x, hxH⟩ ∈ S18.imageBar2 (L ⊔ D.T) L) :
    x ∈ L ⊔ pCoreOf 2 (L ⊔ D.T) := by
  classical
  let H : Subgroup G := L ⊔ D.T
  let x' : ↥H := ⟨x, hxH⟩
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hxL
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hmem : l⁻¹ * x' ∈ (S18.piBar2 H).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
  have hmemO2 : ((l⁻¹ * x' : ↥H) : G) ∈ pCoreOf 2 H := by
    have h2 : l⁻¹ * x' ∈ CFSG.pCore 2 ↥H := by
      rwa [show (S18.piBar2 H).ker = CFSG.pCore 2 ↥H from QuotientGroup.ker_mk' _] at hmem
    rw [← CFSG.openPCoreOf_subgroupOf 2 H] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hxeq : x = (l : G) * ((l⁻¹ * x' : ↥H) : G) := by
    have h1 : l * (l⁻¹ * x') = x' := by group
    have h2 := congrArg (Subtype.val) h1
    simpa [x'] using h2.symm
  rw [hxeq]
  exact Subgroup.mul_mem_sup hlL hmemO2

theorem l33_setup {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hL3 : IsL3Odd (Bar2 L) 3) (hTL : D.T ≤ Subgroup.normalizer (L : Set G)) :
    KYForm (Bar2 (L ⊔ D.T)) (S18.imageBar2 (L ⊔ D.T) L)
      (S18.imageBar2 (L ⊔ D.T) D.T) ∧
      LieModel ↥(S18.imageBar2 (L ⊔ D.T) L) .PSL 3 3 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := L ⊔ D.T
  have hLH : L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hHnorm : H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hTL
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHnorm
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hTH
  have hsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
  obtain ⟨⟨eC⟩, hCnormal, hCsimple, hCnab, -, hcent, hCquot⟩ :=
    S18.fstar_imageBar2_of_normal (H := H) (K := L) (T := D.T)
      hLH hLn hTsyl (by rfl) hL.2.1 hsimple
  have : (S18.imageBar2 H L).Normal := hCnormal
  have hCnab' : ∃ a b : ↥(S18.imageBar2 H L), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hCnab ⟨⟨fun a b => h a b⟩⟩
  have : IsSimpleGroup ↥(S18.imageBar2 H L) := hCsimple
  obtain ⟨hCq, hZbot⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hCnab'
  have hCq' : CFSG.Open.IsQuasisimple ↥(S18.imageBar2 H L) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hCq
  have hodd : Odd (Nat.card (Subgroup.center ↥(S18.imageBar2 H L))) := by
    rw [hZbot]
    simpa using odd_one
  have hcent' : Subgroup.centralizer (S18.imageBar2 H L : Set (Bar2 H)) =
      (Subgroup.center ↥(S18.imageBar2 H L)).map (S18.imageBar2 H L).subtype := by
    rw [hcent, hZbot]
    simp
  obtain ⟨n, hn⟩ := hCquot.exists_card_eq
  have hidx : ∃ a : ℕ, (S18.imageBar2 H L).index = 2 ^ a :=
    ⟨n, (Subgroup.index_eq_card (S18.imageBar2 H L)).trans hn⟩
  have hTsylC : IsSylowIn 2 (S18.imageBar2 H D.T) ⊤ := S18.isSylowIn_imageBar2 hTsyl
  refine ⟨⟨hCnormal, hCq', hodd, hcent', hidx, hTsylC⟩, ?_⟩
  exact CFSG.Blueprint.LieModel.of_mulEquiv eC hL3

private theorem lift_radical {D : Data G} {L : Subgroup G}
    {U : Subgroup (Bar2 (L ⊔ D.T))}
    (hU : IsL33ParabolicRadical (S18.imageBar2 (L ⊔ D.T) L)
      (S18.imageBar2 (L ⊔ D.T) D.T) U) :
    ∃ X : Subgroup ↥(L ⊔ D.T), IsPGroup 3 X ∧ Nat.card X = 9 ∧ ¬ IsCyclic ↥X ∧
      X.map (S18.piBar2 (L ⊔ D.T)) = U ∧
      (X : Set ↥(L ⊔ D.T)) * ((innerT17_8 D L).subgroupOf (L ⊔ D.T)) =
        ((innerT17_8 D L).subgroupOf (L ⊔ D.T)) * X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H : Subgroup G := L ⊔ D.T
  have hTH : D.T ≤ H := le_sup_right
  let S : Subgroup ↥H := (innerT17_8 D L).subgroupOf H
  obtain ⟨-, hUab, hUcard, hUnorm, -⟩ := hU
  have hU3 : IsPGroup 3 U := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hUcard]
    norm_num
  have hS2 : IsPGroup 2 S := by
    have h1 : IsPGroup 2 (innerT17_8 D L) := D.sylowM.isPGroup.to_le inf_le_left
    exact h1.comap_subtype
  have hker : (S18.piBar2 H).ker ≤ S := ker_piBar2_le_innerT17_8
  have hkey : S.map (S18.piBar2 H) =
      S18.imageBar2 H D.T ⊓ S18.imageBar2 H L := by
    rw [show S.map (S18.piBar2 H) = S18.imageBar2 H (innerT17_8 D L) from rfl]
    exact imageBar2_innerT17_8
  have hnorm : S.map (S18.piBar2 H) ≤ Subgroup.normalizer (U : Set (Bar2 H)) := by
    rw [hkey]
    exact hUnorm
  have hpermU : (U : Set (Bar2 H)) * (S.map (S18.piBar2 H) : Set (Bar2 H)) =
      (S.map (S18.piBar2 H) : Set (Bar2 H)) * U :=
    (Subgroup.set_mul_normalizer_comm (S := (S.map (S18.piBar2 H) : Set (Bar2 H)))
      (N := U) hnorm).symm
  obtain ⟨X, hX3, hXmap, ⟨eX⟩, hXperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3) (f := S18.piBar2 H)
      (QuotientGroup.mk'_surjective _) hS2 hker (by norm_num : (3 : ℕ) ≠ 2) hU3 hpermU
  have hUncyc : ¬ IsCyclic ↥U := by
    intro hcyc
    have := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥U)
    have hg3 : g ^ 3 = 1 := by
      ext
      simpa using hUab.2 (g : Bar2 H) g.2
    have hdiv : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    have hle : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
    rw [hg] at hle
    omega
  have hXcard : Nat.card X = 9 := (Nat.card_congr eX.toEquiv).trans hUcard
  have hXncyc : ¬ IsCyclic ↥X := by
    intro hcyc
    have := hcyc
    exact hUncyc (isCyclic_of_surjective eX eX.surjective)
  exact ⟨X, hX3, hXcard, hXncyc, hXmap, hXperm⟩

@[expose] def IsRadical17_8 (D : Data G) (L X : Subgroup G) : Prop :=
  X ≤ L ⊔ D.T ∧ IsPGroup 3 X ∧ Nat.card X = 9 ∧ ¬ IsCyclic X ∧
    Permutes X (innerT17_8 D L) ∧
    ∀ Y : Subgroup G, Y ≤ X → Permutes Y (innerT17_8 D L) → Y = ⊥ ∨ Y = X

private theorem isRadical_of_lift {D : Data G} {L : Subgroup G}
    {U : Subgroup (Bar2 (L ⊔ D.T))} {X : Subgroup ↥(L ⊔ D.T)}
    (hX3 : IsPGroup 3 X) (hXcard : Nat.card X = 9) (hXncyc : ¬ IsCyclic ↥X)
    (hXmap : X.map (S18.piBar2 (L ⊔ D.T)) = U)
    (hXpermG : Permutes (X.map (L ⊔ D.T).subtype) (innerT17_8 D L))
    (hUirr : ∀ E : Subgroup (Bar2 (L ⊔ D.T)), E ≤ U →
      Permutes E (S18.imageBar2 (L ⊔ D.T) D.T ⊓ S18.imageBar2 (L ⊔ D.T) L) →
        E = ⊥ ∨ E = U) :
    IsRadical17_8 D L (X.map (L ⊔ D.T).subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := L ⊔ D.T
  have hXH_le : X.map H.subtype ≤ H := Subgroup.map_subtype_le X
  have hInnerH : innerT17_8 D L ≤ H := by
    refine inf_le_right.trans (sup_le le_sup_left ?_)
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hXsub : (X.map H.subtype).subgroupOf H = X := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_subtype_le X)]
  have hXGmap : S18.imageBar2 H (X.map H.subtype) = U := by
    show ((X.map H.subtype).subgroupOf H).map (S18.piBar2 H) = U
    rw [hXsub]
    exact hXmap
  have hker2 : IsPGroup 2 (S18.piBar2 H).ker := by
    rw [show (S18.piBar2 H).ker = CFSG.pCore 2 ↥H from QuotientGroup.ker_mk' _]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥H)
  have hdisj : X ⊓ (S18.piBar2 H).ker = ⊥ :=
    disjoint_iff.mp
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (S18.piBar2 H).ker hX3 hker2)
  refine ⟨hXH_le, hX3.map H.subtype, ?_, ?_, hXpermG, ?_⟩
  · rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hXcard
  · intro hcyc
    have := hcyc
    let e := Subgroup.equivMapOfInjective X H.subtype Subtype.val_injective
    exact hXncyc (isCyclic_of_surjective e.symm e.symm.surjective)
  · intro Y hYle hYperm
    have hYH : Y ≤ H := hYle.trans hXH_le
    have hYbar_le : S18.imageBar2 H Y ≤ U := by
      rw [← hXGmap]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hYle)
    have hYbar_perm : Permutes (S18.imageBar2 H Y) (S18.imageBar2 H (innerT17_8 D L)) :=
      permutes_imageBar2 hYH hInnerH hYperm
    have hYbar_perm' : Permutes (S18.imageBar2 H Y)
        (S18.imageBar2 H D.T ⊓ S18.imageBar2 H L) := by
      rwa [← imageBar2_innerT17_8]
    have hYsubX : Y.subgroupOf H ≤ X := by
      intro z hz
      have hzX : (z : G) ∈ X.map H.subtype := hYle (Subgroup.mem_subgroupOf.mp hz)
      have hz' : z ∈ (X.map H.subtype).subgroupOf H := Subgroup.mem_subgroupOf.mpr hzX
      rwa [hXsub] at hz'
    rcases hUirr (S18.imageBar2 H Y) hYbar_le hYbar_perm' with hbot | htop
    · left
      have hYsubKer : Y.subgroupOf H ≤ (S18.piBar2 H).ker := by
        intro z hz
        have hz' : S18.piBar2 H z ∈ S18.imageBar2 H Y :=
          Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        rw [hbot] at hz'
        exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hz')
      have hYsubBot : Y.subgroupOf H = ⊥ := by
        have h1 : Y.subgroupOf H ≤ X ⊓ (S18.piBar2 H).ker := le_inf hYsubX hYsubKer
        rw [hdisj] at h1
        exact le_bot_iff.mp h1
      rw [← Subgroup.map_subgroupOf_eq_of_le hYH, hYsubBot, Subgroup.map_bot]
    · right
      have hXY : X ≤ Y.subgroupOf H := by
        intro x hx
        have hxbar : S18.piBar2 H x ∈ S18.imageBar2 H Y := by
          rw [htop, ← hXmap]
          exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxbar
        have hyX : y ∈ X := by
          have hyG : (y : G) ∈ X.map H.subtype := hYle (Subgroup.mem_subgroupOf.mp hy)
          have hy' : y ∈ (X.map H.subtype).subgroupOf H := Subgroup.mem_subgroupOf.mpr hyG
          rwa [hXsub] at hy'
        have hker : y⁻¹ * x ∈ (S18.piBar2 H).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
        have hmem : y⁻¹ * x ∈ X ⊓ (S18.piBar2 H).ker :=
          ⟨X.mul_mem (X.inv_mem hyX) hx, hker⟩
        rw [hdisj] at hmem
        have heq : y⁻¹ * x = 1 := Subgroup.mem_bot.mp hmem
        have hx_eq_y : x = y := by
          have := congrArg (fun z : ↥H => y * z) heq
          simpa using this
        rwa [hx_eq_y]
      have hYX : Y.subgroupOf H = X := le_antisymm hYsubX hXY
      rw [← Subgroup.map_subgroupOf_eq_of_le hYH, hYX]

theorem innerT17_8_mul_mem (hKP : K_L33ParabolicPair) {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL3 : IsL3Odd (Bar2 L) 3)
    (hTL : D.T ≤ normalizer (L : Set G)) :
    ∀ x ∈ D.T, ∀ y ∈ D.T, x ∉ innerT17_8 D L → y ∉ innerT17_8 D L →
      x * y ∈ innerT17_8 D L := by
  classical
  let H : Subgroup G := L ⊔ D.T
  have hTH : D.T ≤ H := le_sup_right
  obtain ⟨hKY, hLie⟩ := l33_setup hL hL3 hTL
  obtain ⟨hparity, -⟩ := hKP (Bar2 H) (S18.imageBar2 H L) (S18.imageBar2 H D.T) hKY hLie
  intro x hx y hy hxS hyS
  have hxH : x ∈ H := hTH hx
  have hyH : y ∈ H := hTH hy
  let x' : ↥H := ⟨x, hxH⟩
  let y' : ↥H := ⟨y, hyH⟩
  have hxT : S18.piBar2 H x' ∈ S18.imageBar2 H D.T :=
    Subgroup.mem_map.mpr ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hyT : S18.piBar2 H y' ∈ S18.imageBar2 H D.T :=
    Subgroup.mem_map.mpr ⟨y', Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hxK : S18.piBar2 H x' ∉ S18.imageBar2 H L := by
    intro hxL
    exact hxS ⟨hx, mem_sup_pCoreOf_of_mem_imageBar2 hxH hxL⟩
  have hyK : S18.piBar2 H y' ∉ S18.imageBar2 H L := by
    intro hyL
    exact hyS ⟨hy, mem_sup_pCoreOf_of_mem_imageBar2 hyH hyL⟩
  have hxyK : S18.piBar2 H x' * S18.piBar2 H y' ∈ S18.imageBar2 H L :=
    hparity (S18.piBar2 H x') hxT (S18.piBar2 H y') hyT hxK hyK
  have hxyH : x * y ∈ H := H.mul_mem hxH hyH
  have hxybar : S18.piBar2 H (⟨x * y, hxyH⟩ : ↥H) ∈ S18.imageBar2 H L := by
    have h1 : (⟨x * y, hxyH⟩ : ↥H) = x' * y' := by
      ext
      rfl
    rw [h1, map_mul]
    exact hxyK
  refine ⟨D.T.mul_mem hx hy, ?_⟩
  simpa [H] using mem_sup_pCoreOf_of_mem_imageBar2 hxyH hxybar

theorem exists_radical_pair_17_8 (hKP : K_L33ParabolicPair) {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL3 : IsL3Odd (Bar2 L) 3)
    (hTL : D.T ≤ normalizer (L : Set G)) :
    ∃ X₁ X₂ : Subgroup G, IsRadical17_8 D L X₁ ∧ IsRadical17_8 D L X₂ ∧
      L ≤ X₁ ⊔ X₂ ⊔ innerT17_8 D L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := L ⊔ D.T
  have hLH : L ≤ H := le_sup_left
  have hInnerH : innerT17_8 D L ≤ H := by
    refine inf_le_right.trans (sup_le le_sup_left ?_)
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 H
  obtain ⟨hKY, hLie⟩ := l33_setup hL hL3 hTL
  obtain ⟨-, U₁, U₂, hU₁, hU₂, hsupU⟩ :=
    hKP (Bar2 H) (S18.imageBar2 H L) (S18.imageBar2 H D.T) hKY hLie
  obtain ⟨X₁, hX₁3, hX₁card, hX₁ncyc, hX₁map, hX₁perm⟩ := lift_radical hU₁
  obtain ⟨X₂, hX₂3, hX₂card, hX₂ncyc, hX₂map, hX₂perm⟩ := lift_radical hU₂
  have hX₁permG : Permutes (X₁.map H.subtype) (innerT17_8 D L) := by
    have h := CFSG.GroupTheory.map_permutes_map H.subtype hX₁perm
    rwa [Subgroup.map_subgroupOf_eq_of_le hInnerH] at h
  have hX₂permG : Permutes (X₂.map H.subtype) (innerT17_8 D L) := by
    have h := CFSG.GroupTheory.map_permutes_map H.subtype hX₂perm
    rwa [Subgroup.map_subgroupOf_eq_of_le hInnerH] at h
  have hUirr₁ : ∀ E : Subgroup (Bar2 H), E ≤ U₁ →
      Permutes E (S18.imageBar2 H D.T ⊓ S18.imageBar2 H L) → E = ⊥ ∨ E = U₁ :=
    hU₁.2.2.2.2
  have hUirr₂ : ∀ E : Subgroup (Bar2 H), E ≤ U₂ →
      Permutes E (S18.imageBar2 H D.T ⊓ S18.imageBar2 H L) → E = ⊥ ∨ E = U₂ :=
    hU₂.2.2.2.2
  have hR₁ : IsRadical17_8 D L (X₁.map H.subtype) :=
    isRadical_of_lift hX₁3 hX₁card hX₁ncyc hX₁map hX₁permG hUirr₁
  have hR₂ : IsRadical17_8 D L (X₂.map H.subtype) :=
    isRadical_of_lift hX₂3 hX₂card hX₂ncyc hX₂map hX₂permG hUirr₂
  refine ⟨X₁.map H.subtype, X₂.map H.subtype, hR₁, hR₂, ?_⟩
  let Jh : Subgroup ↥H := X₁ ⊔ X₂ ⊔ (innerT17_8 D L).subgroupOf H
  have hJhmap : Jh.map (S18.piBar2 H) = S18.imageBar2 H L := by
    have h1 : X₁.map (S18.piBar2 H) = U₁ := hX₁map
    have h2 : X₂.map (S18.piBar2 H) = U₂ := hX₂map
    have h3 : ((innerT17_8 D L).subgroupOf H).map (S18.piBar2 H) =
        S18.imageBar2 H (innerT17_8 D L) := rfl
    change (X₁ ⊔ X₂ ⊔ (innerT17_8 D L).subgroupOf H).map (S18.piBar2 H) =
      S18.imageBar2 H L
    rw [Subgroup.map_sup, Subgroup.map_sup, h1, h2, h3, imageBar2_innerT17_8, hsupU,
      sup_eq_left.mpr inf_le_right]
  have hSleJh : ((innerT17_8 D L).subgroupOf H) ≤ Jh := le_sup_right
  have hkerJ : (S18.piBar2 H).ker ≤ Jh := ker_piBar2_le_innerT17_8.trans hSleJh
  have hLbar_le : (L.subgroupOf H).map (S18.piBar2 H) ≤ Jh.map (S18.piBar2 H) := by
    rw [show (L.subgroupOf H).map (S18.piBar2 H) = S18.imageBar2 H L from rfl, hJhmap]
  have hLJh : L.subgroupOf H ≤ Jh := by
    calc L.subgroupOf H ≤ ((L.subgroupOf H).map (S18.piBar2 H)).comap (S18.piBar2 H) :=
          Subgroup.le_comap_map (S18.piBar2 H) (L.subgroupOf H)
      _ ≤ (Jh.map (S18.piBar2 H)).comap (S18.piBar2 H) := Subgroup.comap_mono hLbar_le
      _ = Jh := Subgroup.comap_map_eq_self hkerJ
  have h := Subgroup.map_mono (f := H.subtype) hLJh
  rw [Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_sup, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hInnerH] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
