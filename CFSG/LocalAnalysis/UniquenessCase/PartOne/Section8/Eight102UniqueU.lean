module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

private theorem map_conj_eq_self_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa using M.mul_mem (M.mul_mem hg hm) (M.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg, ?_⟩
    simp [mul_assoc]

private theorem exists_conj_centralizer_of_le {M S X : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hS : IsSylowOf r S M) {g : G} (hXg : X ≤ M.map (MulAut.conj g).toMonoidHom)
    (hXS : X ≤ S) :
    ∃ c : G, (∀ m ∈ M, c * m * c⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom) ∧
      ∀ y ∈ centralizer (S : Set G), c * y * c⁻¹ ∈ centralizer (X : Set G) := by
  set Mg := M.map (MulAut.conj g).toMonoidHom with hMg
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hSg : IsSylowOf r (S.map (MulAut.conj g).toMonoidHom) Mg := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono hS.le) ?_
    rw [Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj, hS.card_eq]
  have hXr : IsPGroup r (X.subgroupOf Mg) := (hS.isPGroup.to_le hXS).comap_subtype
  obtain ⟨Q, hQ⟩ := hXr.exists_le_sylow
  have hQs : IsSylowOf r ((Q : Subgroup Mg).map Mg.subtype) Mg := ⟨Q, rfl⟩
  obtain ⟨k, hk, hkx⟩ := hSg.exists_mem_conj hQs
  refine ⟨k * g, fun m hm => ?_, fun y hy => ?_⟩
  · have : g * m * g⁻¹ ∈ Mg := ⟨m, hm, by simp⟩
    simpa [mul_assoc] using Mg.mul_mem (Mg.mul_mem hk this) (Mg.inv_mem hk)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxQ : x ∈ (Q : Subgroup Mg).map Mg.subtype :=
      ⟨⟨x, hXg hx⟩, hQ (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
    obtain ⟨s, hs, hsx⟩ := (hkx x).mp hxQ
    have hs' : y * s = s * y := ((Subgroup.mem_centralizer_iff.mp hy) s hs).symm
    have hx' : x = (k * g) * s * (k * g)⁻¹ := by
      have : k⁻¹ * x * k = g * s * g⁻¹ := by simpa using hsx.symm
      calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
        _ = (k * g) * s * (k * g)⁻¹ := by rw [this]; group
    rw [hx']
    calc (k * g) * s * (k * g)⁻¹ * ((k * g) * y * (k * g)⁻¹)
        = (k * g) * (s * y) * (k * g)⁻¹ := by group
      _ = (k * g) * (y * s) * (k * g)⁻¹ := by rw [hs']
      _ = (k * g) * y * (k * g)⁻¹ * ((k * g) * s * (k * g)⁻¹) := by group

theorem mem_uniqueSet_of_centralizer_le {M S X : Subgroup G} {r q : ℕ} (hr : r.Prime)
    (hS : IsSylowOf r S M) (hq : q.Prime) (hqM : IsStronglyPEmbedded q M) {y : G}
    (hyM : y ∈ M) (hyS : y ∈ centralizer (S : Set G)) (hy : orderOf y = q) (hXS : X ≤ S)
    (hXC : centralizer (X : Set G) ≤ M) : X ∈ uniqueSet M := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine ⟨hXS.trans hS.le, fun g hXg => ?_⟩
  by_contra hne
  have hgM : g ∉ M := fun hg => hne (map_conj_eq_self_of_mem hg)
  apply hqM.2.2 g hgM
  obtain ⟨c, hcMg, hcX⟩ := exists_conj_centralizer_of_le hS hXg hXS
  have hy' : c * y * c⁻¹ ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom :=
    ⟨hXC (hcX y hyS), hcMg y hyM⟩
  have hord : orderOf (⟨_, hy'⟩ : ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) = q := by
    rw [Subgroup.orderOf_mk, ← hy]
    exact (SemiconjBy.orderOf_eq c (by simp [SemiconjBy, mul_assoc])).symm
  exact hord ▸ orderOf_dvd_natCard _

private theorem ne_zero_of_isU45 {X : Type} [Group X] {n : ℕ} (hX : IsU45 X n) : n ≠ 0 := by
  rintro rfl
  rcases hX with ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd h (by norm_num)
  · obtain ⟨-, K, _, _, hK, -⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
    rw [pow_zero, one_pow] at hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega

private theorem conj_mem_of_isSylowOf {L P S : Subgroup G} (hP : IsSylowOf 3 P L)
    (hS : IsPGroup 3 S) (hSN : S ≤ normalizer (L : Set G)) (hPS : P ≤ S) {g x : G}
    (hg : g ∈ S) (hx : x ∈ P) : g * x * g⁻¹ ∈ P := by
  obtain ⟨Q, rfl⟩ := hP
  have hxL : x ∈ L := Subgroup.map_subtype_le _ hx
  have hwL : g * x * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSN hg) x).mp hxL
  have hT : IsPGroup 3 ((S ⊓ L).subgroupOf L) := (hS.to_le inf_le_left).comap_subtype
  have hQT : (Q : Subgroup ↥L) ≤ (S ⊓ L).subgroupOf L := fun y hy =>
    Subgroup.mem_subgroupOf.mpr ⟨hPS (Subgroup.mem_map_of_mem L.subtype hy), y.2⟩
  have hw : (⟨g * x * g⁻¹, hwL⟩ : ↥L) ∈ (Q : Subgroup ↥L) := by
    rw [← Q.is_maximal' hT hQT]
    exact Subgroup.mem_subgroupOf.mpr ⟨S.mul_mem (S.mul_mem hg (hPS hx)) (S.inv_mem hg), hwL⟩
  exact ⟨_, hw, rfl⟩

private theorem rhoL_mem_barImage {L P S : Subgroup G} (hP : IsSylowOf 3 P L)
    (hS : IsPGroup 3 S) (hSN : S ≤ normalizer (L : Set G)) (hPS : P ≤ S) :
    ∀ α ∈ (S.subgroupOf (normalizer (L : Set G))).map (rhoL L), ∀ s ∈ barImage L P,
      α s ∈ barImage L P := by
  rintro α ⟨g, hg, rfl⟩ s hs
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hs
  refine uc22p21c_mem_barImage.2 ⟨Subgroup.normalizerMonoidHom L g m, ?_, rfl⟩
  rw [UC6S846.rhoL_mk_coe]
  exact conj_mem_of_isSylowOf hP hS hSN hPS (Subgroup.mem_subgroupOf.mp hg) hm

private theorem exists_lift_orderOf {L : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {xb : Bar2 L} (hxb : orderOf xb = q) :
    ∃ (x : ↥L) (j : ℕ), (QuotientGroup.mk x : Bar2 L) = xb ^ 2 ^ j ∧ orderOf x = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  have hmem : x₀ ^ q ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hxb, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hmem⟩
  have hj' : (x₀ ^ q) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  refine ⟨x₀ ^ 2 ^ j, j, by rw [QuotientGroup.mk_pow], orderOf_eq_prime ?_ ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hj']
  · intro h1
    have h2 : (QuotientGroup.mk x₀ : Bar2 L) ^ 2 ^ j = 1 := by
      rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
    rw [← orderOf_dvd_iff_pow_eq_one, hxb] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))

private theorem exists_centralizing_lift {L S : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hS : IsPGroup 3 S) (hSN : S ≤ normalizer (L : Set G)) {x : ↥L} (hxq : orderOf x = q)
    (hfix : ∀ (s : G) (hs : s ∈ S), rhoL L ⟨s, hSN hs⟩ (QuotientGroup.mk x : Bar2 L) =
      QuotientGroup.mk x) :
    ∃ y ∈ L, orderOf y = q ∧ y ∈ centralizer (S : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hN := UC6S846.normalizer_le_normalizer_pCoreOf L
  have hA : IsPGroup q (zpowers (x : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxq, pow_one])
  have hcomm : ∀ e ∈ S, ∀ a ∈ zpowers (x : G), e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 L := by
    rintro e he a ⟨k, rfl⟩
    have h := (UC6S846.rhoL_fix_iff L ⟨e, hSN he⟩ (x ^ k)).mp
      (by rw [QuotientGroup.mk_zpow, map_zpow, hfix e he])
    simpa using h
  obtain ⟨A', hA'C, hA'L, ⟨φ⟩⟩ := UC6S846.exists_centralizing_copy Nat.prime_three
    (by norm_num) hq hq2 (pCoreOf 2 L) (zpowers (x : G)) S (UC6S846.isPGroup_pCoreOf L)
    (Subgroup.zpowers_le.mpr (hN (Subgroup.le_normalizer x.2))) (hSN.trans hN) hA hS hcomm
  have hcard : q ∣ Nat.card A' := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_zpowers, Subgroup.orderOf_coe, hxq]
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hcard
  refine ⟨y, ?_, by rw [Subgroup.orderOf_coe, hy], hA'C y.2⟩
  exact sup_le (Subgroup.zpowers_le.mpr x.2) (Subgroup.map_subtype_le _) (hA'L y.2)

theorem exists_mem_centralizer_of_torusFix (hK7 : KU45TorusFix) {L P S : Subgroup G} {n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hS : IsPGroup 3 S)
    (hSN : S ≤ normalizer (L : Set G)) (hPS : P ≤ S) :
    ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ n + 1 ∧ ∃ y ∈ L, orderOf y = q ∧ y ∈ centralizer (S : Set G) := by
  obtain ⟨hPb, hPi⟩ := isPGroup_barImage_of_isSylowOf Nat.prime_three hP
  obtain ⟨q, hq, hqd, xb, hxb, -, hfix⟩ := hK7 (Bar2 L) n hX (barImage L P) hPb hPi
    ((S.subgroupOf (normalizer (L : Set G))).map (rhoL L)) (hS.comap_subtype.map _)
    (rhoL_mem_barImage hP hS hSN hPS)
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 : (2 : ℕ) ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (ne_zero_of_isU45 hX))).mp hqd
    exact absurd h1 (by norm_num)
  obtain ⟨x, j, hxj, hxq⟩ := exists_lift_orderOf hq hq2 hxb
  refine ⟨q, hq, hqd, exists_centralizing_lift hq hq2 hS hSN hxq fun s hs => ?_⟩
  rw [hxj, map_pow, hfix _ (Subgroup.mem_map_of_mem _
    (show (⟨s, hSN hs⟩ : ↥(normalizer (L : Set G))) ∈ S.subgroupOf _ from hs))]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
