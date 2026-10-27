module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuterPGL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMax

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 CFSG.GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_le_O2ZIn17_of_card_three {L X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (hXcard : Nat.card X = 3) : ¬ X ≤ (O2ZIn17 L).map L.subtype := by
  intro hle
  have hZ := center_eq_bot_of_isL3 (isL3_one_of_isL2Over17_seven h7)
  have hO : O2ZIn17 L = CFSG.pCore 2 ↥L := by
    unfold O2ZIn17
    rw [hZ, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have h2 : IsPGroup 2 ↥((O2ZIn17 L).map L.subtype) := by
    rw [hO]
    exact CFSG.pCore_isPGroup.map L.subtype
  obtain ⟨k, hk⟩ := (h2.to_le hle).exists_card_eq
  rw [hXcard] at hk
  rcases k with _ | k
  · norm_num at hk
  · rw [pow_succ] at hk
    omega

theorem exists_three_permutes_NTL_of_inner (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hKL : K_L27Local) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X = 3 ∧ Permutes X (NTL17 D L) := by
  classical
  let S : Subgroup G := NTL17 D L
  let N : Subgroup G := L ⊔ S
  have hLN : L ≤ N := le_sup_left
  have hSN : S ≤ N := le_sup_right
  have hST : S ≤ D.T := inf_le_left
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le hST
  have hNnorm : N ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hSNL
  have hLNnormal : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNnorm
  have hTLsyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM) hLM
      ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).mp hL.1)
  have hSinfL : S ⊓ L = D.T ⊓ L := by
    ext x
    constructor
    · rintro ⟨hxS, hxL⟩
      exact ⟨(Subgroup.mem_inf.mp hxS).1, hxL⟩
    · rintro ⟨hxT, hxL⟩
      exact ⟨Subgroup.mem_inf.mpr ⟨hxT, Subgroup.le_normalizer hxL⟩, hxL⟩
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (G := G) (H := S) (K := L) hSNL
  have hS_syl : CFSG.QuasithinUnique.IsSylowTwoOf S N := by
    rw [CFSG.QuasithinUnique.isSylowTwoOf_iff]
    refine ⟨hSN, hS2, ?_⟩
    have hprod' : Nat.card N * Nat.card ↥(S ⊓ L) = Nat.card S * Nat.card L := by
      have h := hprod
      rw [show S ⊔ L = N from sup_comm S L] at h
      exact h
    have hprod'' : Nat.card N * CFSG.QuasithinUnique.twoPart L =
        Nat.card S * Nat.card L := by
      rw [← hprod', hSinfL, hTLsyl.card_eq]
    have hNfac : (Nat.card N).factorization 2 = (Nat.card S).factorization 2 := by
      have h1 := congrArg (fun n : ℕ => n.factorization 2) hprod''
      rw [Nat.factorization_mul (Nat.card_pos (α := ↥N)).ne'
          (CFSG.QuasithinUnique.twoPart_pos L).ne',
        Nat.factorization_mul (Nat.card_pos (α := ↥S)).ne'
          (Nat.card_pos (α := ↥L)).ne',
        Finsupp.add_apply, Finsupp.add_apply] at h1
      have h2 : (CFSG.QuasithinUnique.twoPart L).factorization 2 =
          (Nat.card L).factorization 2 := by
        unfold CFSG.QuasithinUnique.twoPart
        rw [Nat.Prime.factorization_pow Nat.prime_two]
        simp
      rw [h2] at h1
      omega
    have hScard : Nat.card S = 2 ^ (Nat.card S).factorization 2 := by
      obtain ⟨k, hk⟩ := hS2.exists_card_eq
      rw [hk, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [hScard, ← hNfac]
    rfl
  have hSsylOf : CFSG.ABGLocalTools.IsSylowOf 2 S N :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf).mp hS_syl
  have hSsylN : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf N) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) N
      (A := S.subgroupOf N) (B := ⊤)).mp (by
      rw [Subgroup.map_subgroupOf_eq_of_le hSN, Subgroup.map_top, Subgroup.range_subtype]
      exact hSsylOf)
  have hSin : CFSG.Quasithin.IsSylowIn 2 (S.subgroupOf N) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mp hSsylN
  have hSin2 : CFSG.Quasithin.IsSylowIn 2 S N :=
    ⟨hS_syl.1, hS_syl.2.1, hS_syl.2.2⟩
  have hQleS : CFSG.Open.pCoreOf 2 N ≤ S :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSin2
  let π : ↥N →* Bar2 N := QuotientGroup.mk' (CFSG.pCore 2 ↥N)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Sbar : Subgroup (Bar2 N) := (S.subgroupOf N).map π
  have hSbar : CFSG.Quasithin.IsSylowIn 2 Sbar ⊤ :=
    CFSG.Quasithin.E1.isSylowIn_two_map_top hπsurj hSin
  have hL2odd : IsL2Odd (Bar2 N) 7 :=
    isL2Odd_seven_of_isL2Over17_seven (by simpa [N, S] using h7S)
  obtain ⟨⟨Xbar, hXc, hXp, -⟩, -⟩ := hKL (Bar2 N) hL2odd Sbar hSbar
  have hS2N : IsPGroup 2 (S.subgroupOf N) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hkerπ : π.ker ≤ S.subgroupOf N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : ↥N) ∈ CFSG.pCore 2 ↥N := (QuotientGroup.eq_one_iff x).mp hx
    have hx'' : x ∈ (CFSG.Open.pCoreOf 2 N).subgroupOf N := by
      rw [CFSG.openPCoreOf_subgroupOf]
      exact hx'
    exact hQleS (Subgroup.mem_subgroupOf.mp hx'')
  have hNL2 : IsPGroup 2 (↥N ⧸ (L.subgroupOf N)) := by
    have htopNL : L.subgroupOf N ⊔ S.subgroupOf N = ⊤ := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
        Subgroup.map_subgroupOf_eq_of_le hLN, Subgroup.map_subgroupOf_eq_of_le hSN]
    let q : ↥(S.subgroupOf N) →* (↥N ⧸ (L.subgroupOf N)) :=
      (QuotientGroup.mk' (L.subgroupOf N)).comp (S.subgroupOf N).subtype
    have hqsurj : Function.Surjective q := by
      intro y
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf N) y
      have hmem : n ∈ L.subgroupOf N ⊔ S.subgroupOf N := by
        rw [htopNL]
        exact Subgroup.mem_top n
      obtain ⟨l, hl, s, hs, hls⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
      refine ⟨⟨s, hs⟩, ?_⟩
      change (QuotientGroup.mk' (L.subgroupOf N)) (s : ↥N) =
        (QuotientGroup.mk' (L.subgroupOf N)) n
      rw [← hls, map_mul]
      have hl1 : (QuotientGroup.mk' (L.subgroupOf N)) (l : ↥N) = 1 :=
        (QuotientGroup.eq_one_iff l).mpr hl
      rw [hl1, one_mul]
    exact IsPGroup.of_surjective hS2N q hqsurj
  have hsubgrp : ∀ A : Subgroup ↥N, (A.map N.subtype).subgroupOf N = A := by
    intro A
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rwa [N.subtype_injective hwz] at hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have lift_one : ∀ Xbar : Subgroup (Bar2 N), Nat.card Xbar = 3 → Permutes Xbar Sbar →
      ∃ XN : Subgroup ↥N, XN ≤ L.subgroupOf N ∧ Nat.card XN = 3 ∧
        Permutes XN (S.subgroupOf N) ∧ XN.map π = Xbar := by
    intro Xbar hXc hperm
    have hXp : IsPGroup 3 Xbar :=
      IsPGroup.of_card (n := 1) (by rw [hXc]; norm_num)
    obtain ⟨XN, hXNp, hXNmap, ⟨e⟩, hpermN⟩ :=
      CFSG.GroupTheory.exists_permutes_lift π hπsurj hS2N hkerπ (p := 3) (by norm_num)
        hXp hperm
    have hXNcard : Nat.card XN = 3 := by
      rw [← hXc]
      exact Nat.card_congr e.toEquiv
    have hXNleL : XN ≤ L.subgroupOf N := by
      let q : ↥N →* (↥N ⧸ (L.subgroupOf N)) := QuotientGroup.mk' (L.subgroupOf N)
      have htop2 : IsPGroup 2 (⊤ : Subgroup (↥N ⧸ (L.subgroupOf N))) :=
        hNL2.of_equiv Subgroup.topEquiv.symm
      have hmap2 : IsPGroup 2 (XN.map q) := htop2.to_le le_top
      have hmap3 : IsPGroup 3 (XN.map q) := hXNp.map q
      have hbot : XN.map q = ⊥ := by
        have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num)
          (XN.map q) (XN.map q) hmap3 hmap2
        exact disjoint_self.mp hdisj
      intro x hx
      have hxq : q x ∈ XN.map q := Subgroup.mem_map_of_mem q hx
      rw [hbot] at hxq
      exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hxq)
    exact ⟨XN, hXNleL, hXNcard, hpermN, hXNmap⟩
  obtain ⟨XN, hXNle, hXNc, hpermN, -⟩ := lift_one Xbar hXc hXp
  refine ⟨XN.map N.subtype, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_subgroupOf.mp (hXNle hz)
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hXNc]
  · have h := CFSG.GroupTheory.map_permutes_map N.subtype hpermN
    rw [Subgroup.map_subgroupOf_eq_of_le hSN] at h
    exact h

theorem exists_inP11_of_not_le_normalizer (D : Data G) {L X : Subgroup G} (hL : L ∈ calC D.M)
    (h7 : IsL2Over17 (Bar2 L) 7) (hk : D.k = 1)
    (hNT : ¬ D.T ≤ Subgroup.normalizer (L : Set G))
    (hXL : X ≤ L) (hXcard : Nat.card X = 3) (hperm : Permutes X (NTL17 D L)) :
    ∃ X' : Subgroup G, F11.InP11 D X' := by
  obtain ⟨X', hX'M, -, hp, hexp, hnc, hperm'⟩ :=
    exists_permutes_three_of_not_le_normalizer hL hNT hXL hXcard
      (not_le_O2ZIn17_of_card_three h7 hXcard) hperm
  exact ⟨X', inP11_of_strongly Nat.prime_three (by norm_num) (s16c1614_sp_three_of_k_eq_one D hk)
    hX'M hp hexp hnc hperm'⟩

theorem exists_conj_le_T_of_le_normalizer (D : Data G) {L : Subgroup G} {x : G}
    (hx : x ∈ D.M) (hNT : D.T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ w ∈ D.M, L.map (MulAut.conj w).toMonoidHom = L.map (MulAut.conj x).toMonoidHom ∧
      NTL17 D (L.map (MulAut.conj x).toMonoidHom) ≤ D.T.map (MulAut.conj w).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L' : Subgroup G := L.map (MulAut.conj x).toMonoidHom
  let H : Subgroup G := D.M ⊓ Subgroup.normalizer (L : Set G)
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H :=
    D.sylowM.of_le (le_inf D.sylowM.le hNT) inf_le_left
  let R₀ : Subgroup G := (NTL17 D L').comap (MulAut.conj x).toMonoidHom
  have hmemR₀ : ∀ g, g ∈ R₀ ↔ x * g * x⁻¹ ∈ NTL17 D L' := fun g => by
    simp [R₀, MulAut.conj_apply]
  have hconj : ∀ g : G, (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      L'.map (MulAut.conj (x * g * x⁻¹)).toMonoidHom := by
    intro g
    simp only [L', Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hR₀H : R₀ ≤ H := by
    intro g hg
    rw [hmemR₀] at hg
    obtain ⟨hgT, hgN⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : x * g * x⁻¹ ∈ D.M := D.sylowM.le hgT
      have h2 : x⁻¹ * (x * g * x⁻¹) * x ∈ D.M :=
        D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hx) h1) hx
      simpa [mul_assoc] using h2
    · rw [UC6S846.mem_normalizer_iff_map_conj] at hgN ⊢
      apply Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
      rw [hconj g]
      exact hgN
  have hR₀2 : IsPGroup 2 R₀ :=
    (D.sylowM.isPGroup.to_le inf_le_left : IsPGroup 2 (NTL17 D L')).comap_of_injective
      (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  obtain ⟨k, hkH, hk⟩ := UC6.exists_conj_le_of_isSylowOf hTH hR₀H hR₀2
  refine ⟨x * k, D.M.mul_mem hx (Subgroup.mem_inf.mp hkH).1, ?_, ?_⟩
  · have hkL : L.map (MulAut.conj k).toMonoidHom = L :=
      UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.mem_inf.mp hkH).2
    calc L.map (MulAut.conj (x * k)).toMonoidHom
        = (L.map (MulAut.conj k).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
      _ = L.map (MulAut.conj x).toMonoidHom := by rw [hkL]
  · intro r hr
    have hg : x⁻¹ * r * x ∈ R₀ := by
      rw [hmemR₀]
      have hxr : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
      rw [hxr]
      exact hr
    have ht : k⁻¹ * (x⁻¹ * r * x) * k ∈ D.T := hk _ hg
    refine Subgroup.mem_map.mpr ⟨_, ht, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem permutes_NTL17_map_conj (D : Data G) {L X : Subgroup G} (hL : L ∈ calC D.M) {w : G}
    (hw : w ∈ D.M) (hNT : D.T ≤ Subgroup.normalizer (L : Set G)) (hXL : X ≤ L)
    (hperm : Permutes X D.T)
    (hR : NTL17 D (L.map (MulAut.conj w).toMonoidHom) ≤ D.T.map (MulAut.conj w).toMonoidHom) :
    Permutes (X.map (MulAut.conj w).toMonoidHom)
      (NTL17 D (L.map (MulAut.conj w).toMonoidHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : G →* G := (MulAut.conj w).toMonoidHom with hf
  set L' : Subgroup G := L.map f with hL'
  set W : Subgroup G := D.T.map f with hW
  set R : Subgroup G := NTL17 D L' with hRdef
  have hBW : Permutes (X.map f) W := CFSG.GroupTheory.map_permutes_map f hperm
  have hBL' : X.map f ≤ L' := Subgroup.map_mono hXL
  have hRN : R ≤ Subgroup.normalizer (L' : Set G) := inf_le_right
  have hMw : D.M.map f = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hw)
  have hL'C : L' ∈ calC D.M := UC6S846.calC_map D.M _ hMw hL
  have hTL' : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L') L' :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_fo_sylow_inf D.sylowM hL'C.1
  have hTL'R : D.T ⊓ L' ≤ R := le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)
  have hWL'2 : IsPGroup 2 ↥(W ⊓ L') := (D.sylowM.isPGroup.map f).to_le inf_le_left
  have hWL' : W ⊓ L' = D.T ⊓ L' :=
    hTL'.eq_of_le (le_inf (hTL'R.trans hR) inf_le_right) inf_le_right hWL'2
  have hWLR : W ⊓ (L' ⊔ R) = R := by
    apply le_antisymm
    · rintro g ⟨hgW, hgLR⟩
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left L' R hRN
      have hg' : g ∈ (L' : Set G) * (R : Set G) := by
        rw [← hset]
        exact hgLR
      obtain ⟨l, hl, r, hr, rfl⟩ := hg'
      have hlW : l ∈ W := by
        have := W.mul_mem hgW (W.inv_mem (hR hr))
        simpa using this
      have hlTL : l ∈ D.T ⊓ L' := by
        rw [← hWL']
        exact ⟨hlW, hl⟩
      exact R.mul_mem (hTL'R hlTL) hr
    · exact le_inf hR le_sup_right
  have h := CFSG.GroupTheory.permutes_inf_of_le (B := X.map f) (T := W) (N := L' ⊔ R)
    (hBL'.trans le_sup_left) hBW
  rw [hWLR] at h
  exact h

theorem card_imageOTwoQuot_eq_three {D : Data G} {X : Subgroup G} (hXM : X ≤ D.M)
    (hXcard : Nat.card X = 3) : Nat.card ↥(CFSG.Quasithin.imageOTwoQuot D.M X) = 3 := by
  have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M X hXM
  have h2 : Nat.card ↥(X ⊓ CFSG.Open.pCoreOf 2 D.M) = 1 := by
    have hdvd : Nat.card ↥(X ⊓ CFSG.Open.pCoreOf 2 D.M) ∣ 3 := by
      rw [← hXcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2p : IsPGroup 2 ↥(X ⊓ CFSG.Open.pCoreOf 2 D.M) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le inf_le_right
    obtain ⟨k, hk⟩ := h2p.exists_card_eq
    rw [hk] at hdvd ⊢
    have hk2 : k ≤ 1 := by
      by_contra hkk
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle : 2 ^ k ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases k
    · norm_num
    · norm_num at hdvd
  rw [hXcard, h2, mul_one] at h
  exact h.symm

theorem pow_three_of_mem_imageOTwoQuot {D : Data G} {X : Subgroup G} (hXcard : Nat.card X = 3) :
    ∀ a ∈ CFSG.Quasithin.imageOTwoQuot D.M X, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨x, hxM, hxX, rfl⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp ha
  have hx3 : x ^ 3 = 1 := by
    have hdvd : orderOf x ∣ 3 := by
      rw [← hXcard]
      exact Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · rw [orderOf_eq_one_iff.mp h1]
      simp
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h3])
  calc (QuotientGroup.mk ⟨x, hxM⟩ : Mbar9 D) ^ 3
      = QuotientGroup.mk ((⟨x, hxM⟩ : ↥D.M) ^ 3) := by
        rw [← QuotientGroup.mk_pow]
    _ = QuotientGroup.mk 1 := by
        rw [show (⟨x, hxM⟩ : ↥D.M) ^ 3 = 1 from Subtype.ext (by simpa using hx3)]
    _ = 1 := by
        change (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) (1 : ↥D.M) = 1
        exact map_one _

theorem exists_permutes_of_Mbar9 (D : Data G) {E : Subgroup (Mbar9 D)} (hEne : E ≠ ⊥)
    (hE3 : IsPGroup 3 ↥E) (hEexp : ∀ e ∈ E, e ^ 3 = 1) (hEnc : ¬ IsCyclic ↥E)
    (hEperm : Permutes E (Tbar9 D)) :
    ∃ X' : Subgroup G, X' ≤ D.M ∧ X' ≠ ⊥ ∧ IsPGroup 3 ↥X' ∧ (∀ x ∈ X', x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X' ∧ Permutes X' D.T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
      hE3 (by rw [hSmap]; exact hEperm)
  refine ⟨P.map D.M.subtype, Subgroup.map_subtype_le P, ?_, hP3.map D.M.subtype, ?_, ?_, ?_⟩
  · intro hbot
    have hPbot : P = ⊥ := by
      refine Subgroup.map_injective (f := D.M.subtype) Subtype.val_injective ?_
      simpa using hbot
    have hcard : Nat.card E = 1 := by
      have h := Nat.card_congr eP.toEquiv
      rw [hPbot, Subgroup.card_bot] at h
      exact h.symm
    exact hEne ((Subgroup.card_eq_one).mp hcard)
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy3 : (⟨y, hy⟩ : ↥P) ^ 3 = 1 := by
      apply eP.injective
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using hEexp _ (eP ⟨y, hy⟩).2)
    simpa using congrArg (fun z : ↥P => ((z : ↥D.M) : G)) hy3
  · intro hcyc
    have hPcyc : IsCyclic ↥P := by
      let e := Subgroup.equivMapOfInjective P D.M.subtype Subtype.val_injective
      exact @isCyclic_of_surjective ↥P ↥(P.map D.M.subtype) _ _
        (↥(P.map D.M.subtype) ≃* ↥P) hcyc _ _ e.symm e.symm.surjective
    exact hEnc (@isCyclic_of_surjective ↥E ↥P _ _ (↥P ≃* ↥E) hPcyc _ _ eP
      eP.surjective)
  · have hDT : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) = (D.T : Set G) :=
      congrArg (fun H : Subgroup G => (H : Set G)) (Subgroup.map_subgroupOf_eq_of_le D.sylowM.le)
    have hXcoe : (P.map D.M.subtype : Set G) = D.M.subtype '' (P : Set ↥D.M) := rfl
    have hScoe : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) =
        D.M.subtype '' (D.T.subgroupOf D.M : Set ↥D.M) := rfl
    show ((P.map D.M.subtype : Subgroup G) : Set G) * (D.T : Set G) =
      (D.T : Set G) * ((P.map D.M.subtype : Subgroup G) : Set G)
    rw [hXcoe, ← hDT, hScoe, ← Set.image_mul, ← Set.image_mul, hPperm]

theorem exists_noncyclic_permutes_of_two_components (D : Data G) {L L' X B : Subgroup G}
    (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M) (hne : L' ≠ L) (h7 : IsL2Over17 (Bar2 L) 7)
    (hXL : X ≤ L) (hBL : B ≤ L') (hXc : Nat.card X = 3) (hBc : Nat.card B = 3)
    (hXp : Permutes X D.T) (hBp : Permutes B D.T) :
    ∃ X' : Subgroup G, X' ≤ D.M ∧ X' ≠ ⊥ ∧ IsPGroup 3 ↥X' ∧ (∀ x ∈ X', x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X' ∧ Permutes X' D.T := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hL'M : L' ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL'.1
  have hXM : X ≤ D.M := hXL.trans hLM
  have hBM : B ≤ D.M := hBL.trans hL'M
  have hTM : D.T ≤ D.M := D.sylowM.le
  let A : Subgroup (Mbar9 D) := CFSG.Quasithin.imageOTwoQuot D.M X
  let Bb : Subgroup (Mbar9 D) := CFSG.Quasithin.imageOTwoQuot D.M B
  have hAK : A ≤ K1Nine D L := CFSG.Quasithin.imageOTwoQuot_mono hXL
  have hBK : Bb ≤ K1Nine D L' := CFSG.Quasithin.imageOTwoQuot_mono hBL
  have hAc : Nat.card A = 3 := card_imageOTwoQuot_eq_three hXM hXc
  have hBc' : Nat.card Bb = 3 := card_imageOTwoQuot_eq_three hBM hBc
  have hAexp : ∀ a ∈ A, a ^ 3 = 1 := pow_three_of_mem_imageOTwoQuot hXc
  have hBexp : ∀ b ∈ Bb, b ^ 3 = 1 := pow_three_of_mem_imageOTwoQuot hBc
  have hAnc : ¬ A ≤ (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype :=
    imageOTwoQuot_not_le_center_of_not_le_O2Z hL hXL (not_le_O2ZIn17_of_card_three h7 hXc)
  have hAp : Permutes A (Tbar9 D) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13xf_map_permutes hXM hTM hXp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M))
  have hBp' : Permutes Bb (Tbar9 D) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13xf_map_permutes hBM hTM hBp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M))
  have hKne : K1Nine D L' ≠ K1Nine D L := fun h =>
    hne (eq_of_mem_calC_of_imageOTwoQuot_eq hL' hL h)
  have hcomm : ∀ a ∈ K1Nine D L', ∀ b ∈ K1Nine D L, a * b = b * a := fun a ha b hb =>
    CFSG.StandardType.ggCommute_of_isComponent_ne (isComponent_K1 hL) (isComponent_K1 hL')
      hKne ha hb
  have hBA : Bb ≤ Subgroup.normalizer (A : Set (Mbar9 D)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A : Set (Mbar9 D)))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hcomm b (hBK hb) a (hAK ha)).symm
  have hEset : ((A ⊔ Bb : Subgroup (Mbar9 D)) : Set (Mbar9 D)) = (A : Set _) * (Bb : Set _) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A Bb hBA
  have hEperm : Permutes (A ⊔ Bb) (Tbar9 D) := by
    unfold Permutes
    rw [hEset, mul_assoc, hBp', ← mul_assoc, hAp, mul_assoc]
  have hEexp : ∀ e ∈ A ⊔ Bb, e ^ 3 = 1 := by
    intro e he
    have he' : e ∈ (A : Set (Mbar9 D)) * (Bb : Set (Mbar9 D)) := by
      rw [← hEset]
      exact he
    obtain ⟨a, ha, b, hb, rfl⟩ := he'
    have hab : Commute a b := (hcomm b (hBK hb) a (hAK ha)).symm
    rw [hab.mul_pow, hAexp a ha, hBexp b hb, one_mul]
  have hE3 : IsPGroup 3 ↥(A ⊔ Bb) := fun g =>
    ⟨1, Subtype.ext (by simpa using hEexp g g.2)⟩
  have hAE : A ≤ A ⊔ Bb := le_sup_left
  have hBE : Bb ≤ A ⊔ Bb := le_sup_right
  have hEnc : ¬ IsCyclic ↥(A ⊔ Bb) := by
    intro hcyc
    have := hcyc
    have hcard : Nat.card ↥(A.subgroupOf (A ⊔ Bb)) = Nat.card ↥(Bb.subgroupOf (A ⊔ Bb)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv, hAc, hBc']
    have heq : A.subgroupOf (A ⊔ Bb) = Bb.subgroupOf (A ⊔ Bb) :=
      IsCyclic.subgroup_eq_iff_card_eq.2 hcard
    have hAB : A = Bb := by
      have h := congrArg (fun H => H.map (A ⊔ Bb).subtype) heq
      simpa [Subgroup.map_subgroupOf_eq_of_le hAE, Subgroup.map_subgroupOf_eq_of_le hBE] using h
    apply hAnc
    intro a ha
    have haK : a ∈ K1Nine D L := hAK ha
    have haK' : a ∈ K1Nine D L' := hBK (hAB ▸ ha)
    refine ⟨⟨a, haK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (hcomm a haK' k k.2).symm
  have hEne : A ⊔ Bb ≠ ⊥ := by
    intro hbot
    have hA1 : A = ⊥ := le_bot_iff.mp (hbot ▸ hAE)
    have : Nat.card A = 1 := by rw [hA1, Subgroup.card_bot]
    omega
  exact exists_permutes_of_Mbar9 D hEne hE3 hEexp hEnc hEperm

theorem inP11_or_pgl_of_conj (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hKL : K_L27Local) (h7 : IsL2Over17 (Bar2 L) 7) (hk : D.k = 1) {x : G} (hx : x ∈ D.M)
    (hxL : L.map (MulAut.conj x).toMonoidHom ≠ L) :
    (∃ X : Subgroup G, F11.InP11 D X) ∨
      CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)) := by
  rcases (bar2_sup_data (L := L) (R := NTL17 D L)
      (D.sylowM.isPGroup.to_le inf_le_left) inf_le_right h7).2 with hin | hpgl
  · left
    obtain ⟨X, hXL, hXc, hXp⟩ := exists_three_permutes_NTL_of_inner D hL hin hKL
    by_cases hNT : D.T ≤ Subgroup.normalizer (L : Set G)
    · have hS : NTL17 D L = D.T := inf_eq_left.mpr hNT
      rw [hS] at hXp
      obtain ⟨w, hwM, hwL, hR⟩ := exists_conj_le_T_of_le_normalizer D hx hNT
      rw [← hwL] at hR hxL
      have hB := permutes_NTL17_map_conj D hL hwM hNT hXL hXp hR
      have hMw : D.M.map (MulAut.conj w).toMonoidHom = D.M :=
        UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hwM)
      have hL' : L.map (MulAut.conj w).toMonoidHom ∈ calC D.M :=
        UC6S846.calC_map D.M _ hMw hL
      have hBL : X.map (MulAut.conj w).toMonoidHom ≤ L.map (MulAut.conj w).toMonoidHom :=
        Subgroup.map_mono hXL
      have hBc : Nat.card (X.map (MulAut.conj w).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hXc]
      by_cases hNT' : D.T ≤
          Subgroup.normalizer ((L.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G)
      ·
        have hS' : NTL17 D (L.map (MulAut.conj w).toMonoidHom) = D.T := inf_eq_left.mpr hNT'
        rw [hS'] at hB
        obtain ⟨X', hX'M, -, hp, hexp, hnc, hperm'⟩ :=
          exists_noncyclic_permutes_of_two_components D hL hL' hxL h7 hXL hBL hXc hBc hXp hB
        exact ⟨X', inP11_of_strongly Nat.prime_three (by norm_num)
          (s16c1614_sp_three_of_k_eq_one D hk) hX'M hp hexp hnc hperm'⟩
      ·
        have h7' : IsL2Over17 (Bar2 (L.map (MulAut.conj w).toMonoidHom)) 7 :=
          isL2Over17_of_mulEquiv (UC6S846.bar2Equiv (L.equivMapOfInjective
            (MulAut.conj w).toMonoidHom (MulAut.conj w).injective)).symm h7
        exact exists_inP11_of_not_le_normalizer D hL' h7' hk hNT' hBL hBc hB
    ·
      exact exists_inP11_of_not_le_normalizer D hL h7 hk hNT hXL hXc hXp
  · exact Or.inr hpgl

theorem gap17_15_P_of (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (hKL : K_L27Local) : Gap17_15_P D V₀ V L r q hC :=
  fun h7 hk _ hx _ _ hxL _ _ => inP11_or_pgl_of_conj D hC.memL hKL h7 hk hx hxL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
