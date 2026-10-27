module

public import CFSG.Timmesfeld.Bridge.OddRootDefs
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.Timmesfeld.Bridge

theorem mem_pCore_of_mem_zStar_of_two_pow {H : Type*} [Group H] {x : H}
    (hxZ : x ∈ zStar H) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ CFSG.pCore 2 H := by
  let Q := CFSG.pCore 2 H
  let ρ := QuotientGroup.mk' Q
  have hxZc : ρ x ∈ Subgroup.center (H ⧸ Q) := by
    simpa [zStar, Q, ρ] using hxZ
  obtain ⟨k, hk⟩ := hx
  have hk' : (ρ x) ^ 2 ^ k = 1 := by
    rw [← map_pow, hk, map_one]
  have hcard : Nat.card (Subgroup.zpowers (ρ x)) ∣ 2 ^ k := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk'
  have hp : IsPGroup 2 (Subgroup.zpowers (ρ x)) := IsPGroup.of_card_dvd_pow hcard
  have hnormal : (Subgroup.zpowers (ρ x)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hxZc)
  have hKn : ((Subgroup.zpowers (ρ x)).comap ρ).Normal := hnormal.comap ρ
  have hK2 : IsPGroup 2 ((Subgroup.zpowers (ρ x)).comap ρ) :=
    hp.comap_of_ker_isPGroup ρ (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
  exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hKn hK2 (by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_zpowers (ρ x))

end CFSG.Timmesfeld.Bridge

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.BenderSuzuki CFSG.CGT.Timmesfeld75
  CFSG.LieType.Ree CFSG.Blueprint
open scoped MatrixGroups

variable {Y : Type*} [Group Y]

theorem SqOut.map {Y' : Type*} [Group Y'] (φ : Y →* Y') (hφ : IsPGroup 2 φ.ker)
    (h : SqOut Y) : SqOut Y' := by
  obtain ⟨g, ⟨k, hk⟩, hg⟩ := h
  refine ⟨φ g, ⟨k, by rw [← map_pow, hk, map_one]⟩, ?_⟩
  intro hmem
  have hmem' : g ^ 2 ∈ (CFSG.pCore 2 Y').comap φ := by
    rw [Subgroup.mem_comap, map_pow]
    exact hmem
  have hKn : ((CFSG.pCore 2 Y').comap φ).Normal := inferInstance
  have hK2 : IsPGroup 2 ((CFSG.pCore 2 Y').comap φ) :=
    (CFSG.pCore_isPGroup (p := 2) (G := Y')).comap_of_ker_isPGroup φ hφ
  exact hg (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hKn hK2 hmem')

theorem SqOut.of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') (h : SqOut Y) :
    SqOut Y' := by
  refine SqOut.map e.toMonoidHom ?_ h
  rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective]
  exact IsPGroup.of_bot

private theorem exists_order_four_szModel (n : ℕ) :
    ∃ x : SzModel n, x ^ 2 ≠ 1 ∧ x ^ 4 = 1 := by
  let K := GaloisField 2 (2 * n + 1)
  have hK : Nat.card K = 2 ^ (2 * n + 1) := GaloisField.card 2 (2 * n + 1) (by omega)
  let e : suzukiGroup n K ≃* SzModel n :=
    (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).trans
      (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n).symm)
  let s : suzukiGroup n K := suzukiSElt n K 1 0
  have htwo : (2 : K) = 0 := (suzuki_frob_data n hK).1
  have hs2 : s ^ 2 = suzukiSElt n K 0 1 := by
    rw [pow_two, suzukiSElt_mul hK]
    congr 1
    · linear_combination htwo
    · simp
  have hs1 : suzukiSElt n K 0 1 ^ 2 = 1 := by
    rw [pow_two, suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK]
    congr 1
    · simp
    · linear_combination htwo
  have hs01 : suzukiSElt n K 0 1 ≠ 1 := by
    intro h
    have hz : suzukiSElt n K 0 1 = suzukiSElt n K 0 0 := by
      rw [h, ← suzukiSElt_zero_zero (a := n) (K := K) hK]
    have h' := (suzukiSElt_inj (a := n) (K := K)).mp hz
    exact one_ne_zero h'.2
  have hs4 : s ^ 4 = 1 := by
    calc s ^ 4 = s ^ (2 * 2) := by norm_num
      _ = (s ^ 2) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [hs2, hs1]
  refine ⟨e s, ?_, ?_⟩
  · intro h
    have hs2eq : s ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, h, map_one]
    exact hs01 (hs2 ▸ hs2eq)
  · rw [← map_pow, hs4, map_one]

theorem sqOut_of_sz (n : ℕ)
    (e : Y ⧸ CFSG.pCore 2 Y ≃* SzModel n) : SqOut Y := by
  obtain ⟨x, hx2, hx4⟩ := exists_order_four_szModel n
  let Q := CFSG.pCore 2 Y
  let q : Y ⧸ Q := e.symm x
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective Q q
  have hq4 : q ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, e.apply_symm_apply x, hx4, map_one]
  have hg4Q : g ^ 4 ∈ Q := by
    refine (QuotientGroup.eq_one_iff (N := Q) (g ^ 4)).mp ?_
    change QuotientGroup.mk' Q (g ^ 4) = 1
    rw [map_pow, show QuotientGroup.mk' Q g = q from hg, hq4]
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)) ⟨g ^ 4, hg4Q⟩
  have hm' : (g ^ 4) ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  refine ⟨g, ⟨m + 2, ?_⟩, ?_⟩
  · rw [show 2 ^ (m + 2) = 4 * 2 ^ m by rw [pow_add]; ring, pow_mul, hm']
  · intro hg2Q
    have hx2' : e (QuotientGroup.mk' Q (g ^ 2)) ≠ 1 := by
      rw [show QuotientGroup.mk' Q (g ^ 2) = q ^ 2 by rw [map_pow, hg]]
      rw [map_pow, show q = e.symm x from rfl, e.apply_symm_apply x]
      exact hx2
    have h1 : QuotientGroup.mk' Q (g ^ 2) = 1 :=
      (QuotientGroup.eq_one_iff (N := Q) (g ^ 2)).mpr hg2Q
    exact hx2' (by rw [h1, map_one])

theorem not_sqOut_of_map_le {H : Type*} [Group H] {Y : Subgroup H}
    {A : Subgroup (H ⧸ zStar H)}
    (hYA : Y.map (QuotientGroup.mk' (zStar H)) ≤ A)
    (hA : ∀ a ∈ A, (∃ k : ℕ, a ^ 2 ^ k = 1) → a ^ 2 = 1) : ¬ SqOut Y := by
  rintro ⟨g, ⟨k, hk⟩, hg⟩
  let π := QuotientGroup.mk' (zStar H)
  let x : H := g
  have hxA : π x ∈ A := hYA ⟨g, g.2, rfl⟩
  have hxpow : ∃ m : ℕ, (π x) ^ 2 ^ m = 1 := by
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : x ^ 2 ^ k = 1 := by
      simpa [x] using congrArg Subtype.val hk
    rw [this, map_one]
  have hsq : (π x) ^ 2 = 1 := hA _ hxA hxpow
  have hx2Z : x ^ 2 ∈ zStar H := by
    refine (QuotientGroup.eq_one_iff (N := zStar H) (x ^ 2)).mp ?_
    change π (x ^ 2) = 1
    rw [map_pow]
    simpa [pow_two] using hsq
  have hx2pow : ∃ m : ℕ, (x ^ 2) ^ 2 ^ m = 1 := by
    have hdvd : orderOf (x ^ 2) ∣ 2 ^ k :=
      (orderOf_pow_dvd (x := x) 2).trans
        (orderOf_dvd_of_pow_eq_one (by simpa [x] using congrArg Subtype.val hk))
    exact ⟨k, (orderOf_dvd_iff_pow_eq_one).mp hdvd⟩
  have hpc : x ^ 2 ∈ CFSG.pCore 2 H :=
    mem_pCore_of_mem_zStar_of_two_pow hx2Z hx2pow
  have hK2 : IsPGroup 2 ((CFSG.pCore 2 H).comap Y.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := H)).comap_of_injective Y.subtype
      Y.subtype_injective
  have hKn : ((CFSG.pCore 2 H).comap Y.subtype).Normal :=
    (CFSG.pCore_normal (p := 2) (G := H)).comap Y.subtype
  have hle : (CFSG.pCore 2 H).comap Y.subtype ≤ CFSG.pCore 2 Y :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hKn hK2
  have hmem : (g : Y) ^ 2 ∈ (CFSG.pCore 2 H).comap Y.subtype := by
    rw [Subgroup.mem_comap]
    simpa [x] using hpc
  exact hg (hle hmem)

theorem not_sqOut_of_isPGroup {Y : Type*} [Group Y] (hY : IsPGroup 2 Y) :
    ¬ SqOut Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨g, -, hg⟩
  have htop : CFSG.pCore 2 Y = ⊤ :=
    eq_top_iff.mpr (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (G := Y) (p := 2)
      (H := ⊤) inferInstance (hY.to_subgroup ⊤))
  exact hg (by rw [htop]; exact Subgroup.mem_top _)

theorem sqOut_subgroupOf_iff {G : Type*} [Group G] {X H : Subgroup G} (hXH : X ≤ H) :
    SqOut (X.subgroupOf H) ↔ SqOut X :=
  ⟨fun h => SqOut.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH) h,
    fun h => SqOut.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH).symm h⟩

end CFSG.Timmesfeld.Bridge.OddRoot
