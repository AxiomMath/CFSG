module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SevenLocal17
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMax
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.LiftPermutes
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_15_swapPairInner_of (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (hKL : K_L27Local) :
    Gap17_15_swapPairInner D V₀ V L r q hC := by
  intro h7 _ h7S _
  classical
  let S : Subgroup G := NTL17 D L
  let N : Subgroup G := L ⊔ S
  have hLN : L ≤ N := le_sup_left
  have hSN : S ≤ N := le_sup_right
  have hST : S ≤ D.T := inf_le_left
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le hST
  have hNnorm : N ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hSNL
  have hLNnormal : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNnorm
  have hTLsyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM) hLM
      ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).mp hC.memL.1)
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
  obtain ⟨-, Xbar₁, Xbar₂, hc₁, hc₂, -, hp₁, hp₂, hsup, -, -⟩ :=
    hKL (Bar2 N) hL2odd Sbar hSbar
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
  obtain ⟨XN₁, hXN₁le, hX₁c, hperm₁N, hX₁map⟩ := lift_one Xbar₁ hc₁ hp₁
  obtain ⟨XN₂, hXN₂le, hX₂c, hperm₂N, hX₂map⟩ := lift_one Xbar₂ hc₂ hp₂
  let X₁ : Subgroup G := XN₁.map N.subtype
  let X₂ : Subgroup G := XN₂.map N.subtype
  have hX₁L : X₁ ≤ L := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp (show y ∈ XN₁.map N.subtype from hy)
    exact Subgroup.mem_subgroupOf.mp (hXN₁le hz)
  have hX₂L : X₂ ≤ L := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp (show y ∈ XN₂.map N.subtype from hy)
    exact Subgroup.mem_subgroupOf.mp (hXN₂le hz)
  have hX₁card : Nat.card X₁ = 3 := by
    change Nat.card ↥(XN₁.map N.subtype) = 3
    rw [Subgroup.card_map_of_injective N.subtype_injective, hX₁c]
  have hX₂card : Nat.card X₂ = 3 := by
    change Nat.card ↥(XN₂.map N.subtype) = 3
    rw [Subgroup.card_map_of_injective N.subtype_injective, hX₂c]
  have hperm₁ : Permutes X₁ S := by
    have h := CFSG.GroupTheory.map_permutes_map N.subtype hperm₁N
    rw [Subgroup.map_subgroupOf_eq_of_le hSN] at h
    exact h
  have hperm₂ : Permutes X₂ S := by
    have h := CFSG.GroupTheory.map_permutes_map N.subtype hperm₂N
    rw [Subgroup.map_subgroupOf_eq_of_le hSN] at h
    exact h
  have hX₁N : X₁ ≤ N := by
    change XN₁.map N.subtype ≤ N
    exact Subgroup.map_subtype_le _
  have hX₂N : X₂ ≤ N := by
    change XN₂.map N.subtype ≤ N
    exact Subgroup.map_subtype_le _
  have hsub₁ : X₁.subgroupOf N = XN₁ := by
    change (XN₁.map N.subtype).subgroupOf N = XN₁
    exact hsubgrp XN₁
  have hsub₂ : X₂.subgroupOf N = XN₂ := by
    change (XN₂.map N.subtype).subgroupOf N = XN₂
    exact hsubgrp XN₂
  have himageTop : ((X₁ ⊔ X₂ ⊔ S).subgroupOf N).map π = ⊤ := by
    rw [Subgroup.subgroupOf_sup (sup_le hX₁N hX₂N) hSN,
      Subgroup.subgroupOf_sup hX₁N hX₂N,
      Subgroup.map_sup, Subgroup.map_sup, hsub₁, hsub₂, hX₁map, hX₂map]
    change Xbar₁ ⊔ Xbar₂ ⊔ Sbar = ⊤
    rw [show Xbar₁ ⊔ Xbar₂ ⊔ Sbar = Sbar ⊔ Xbar₁ ⊔ Xbar₂ from by ac_rfl]
    exact hsup
  refine ⟨X₁, X₂, hX₁L, hX₂L, hX₁card, hX₂card, hperm₁, hperm₂, ?_⟩
  intro l hl
  have hlN : l ∈ N := hLN hl
  have hmem : π ⟨l, hlN⟩ ∈ ((X₁ ⊔ X₂ ⊔ S).subgroupOf N).map π := by
    rw [himageTop]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hq⟩ := Subgroup.mem_map.mp hmem
  have hqker : (⟨l, hlN⟩ : ↥N) * h⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hq, mul_inv_cancel]
  have hqle : (⟨l, hlN⟩ : ↥N) * h⁻¹ ∈ S.subgroupOf N := hkerπ hqker
  have hl_eq : l = (((⟨l, hlN⟩ : ↥N) * h⁻¹ : ↥N) * h : ↥N) := by
    have h1 : (⟨l, hlN⟩ : ↥N) = ((⟨l, hlN⟩ : ↥N) * h⁻¹) * h := by group
    exact congrArg (fun z : ↥N => (z : G)) h1
  rw [hl_eq]
  have hhH : (h : G) ∈ X₁ ⊔ X₂ ⊔ S := by
    simpa using (Subgroup.mem_subgroupOf.mp hh)
  have hqH : (((⟨l, hlN⟩ : ↥N) * h⁻¹ : ↥N) : G) ∈ X₁ ⊔ X₂ ⊔ S :=
    Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hqle)
  exact (sup_le_sup_left hST (X₁ ⊔ X₂)) (Subgroup.mul_mem _ hqH hhH)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
