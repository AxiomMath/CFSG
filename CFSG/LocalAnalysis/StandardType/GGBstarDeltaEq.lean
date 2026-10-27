module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.LargeEvenClassification.LocalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreTwoSubgroups
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace BstarEq

open Subgroup
open scoped Pointwise

section Cyclic

variable {W : Type*} [Group W] [Finite W]

theorem pow_eq_one_of_fix {p k : ℕ} [IsCyclic W] (hW : Nat.card W = p ^ (k + 1))
    (σ : MulAut W) {x : W} (hx : orderOf x = p) (hσx : σ x = x) : σ ^ p ^ k = 1 := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
  have hm' : ∀ g : W, σ g = g ^ m := fun g => hm g
  have h1 : (p : ℤ) ∣ m - 1 := by
    have hpow : x ^ (m - 1) = 1 := by
      rw [zpow_sub_one, ← hm' x, hσx, mul_inv_cancel]
    rw [← hx]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hpow
  have h2 := dvd_sub_pow_of_dvd_sub h1 k
  rw [one_pow] at h2
  obtain ⟨c, hc⟩ := h2
  push_cast at hc
  have hiter : ∀ j : ℕ, ∀ g : W, (σ ^ j) g = g ^ (m ^ j) := by
    intro j
    induction j with
    | zero => intro g; simp
    | succ j ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, ih, map_zpow, hm', ← zpow_mul, pow_succ']
  ext g
  rw [hiter, MulAut.one_apply]
  have hg : g ^ ((p : ℤ) ^ (k + 1)) = 1 := by
    have h := pow_card_eq_one' (G := W) (x := g)
    rw [hW] at h
    exact_mod_cast h
  have hm1 : m ^ p ^ k = 1 + (p : ℤ) ^ (k + 1) * c := by linarith
  rw [hm1, zpow_add, zpow_one, zpow_mul, hg, one_zpow, mul_one]

end Cyclic

section Burnside

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]

theorem normalizer_le_centralizer_of_central (W : Sylow p Y) (hWc : IsCyclic (W : Subgroup Y))
    {x : Y} (hxW : x ∈ (W : Subgroup Y)) (hx : orderOf x = p) (hxZ : x ∈ center Y) :
    normalizer ((W : Subgroup Y) : Set Y) ≤ centralizer ((W : Subgroup Y) : Set Y) := by
  intro n hn
  set f := (W : Subgroup Y).normalizerMonoidHom with hf
  set σ := f ⟨n, hn⟩ with hσ
  obtain ⟨k', hk'⟩ := W.isPGroup'.exists_card_eq
  have hk0 : k' ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk'
    have hbot := Subgroup.eq_bot_of_card_eq _ hk'
    have hx1 : x = 1 := by
      rw [hbot] at hxW
      exact hxW
    rw [hx1, orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hσx : σ ⟨x, hxW⟩ = ⟨x, hxW⟩ := by
    apply Subtype.ext
    show n * x * n⁻¹ = x
    rw [mem_center_iff.mp hxZ n, mul_inv_cancel_right]
  have hxo : orderOf (⟨x, hxW⟩ : (W : Subgroup Y)) = p := by
    rw [Subgroup.orderOf_mk, hx]
  have hσp : σ ^ p ^ k = 1 := pow_eq_one_of_fix hk' σ hxo hσx
  have hdvd1 : orderOf σ ∣ p ^ k := orderOf_dvd_of_pow_eq_one hσp
  have hdvd2 : orderOf σ ∣ Nat.card f.range := Subgroup.orderOf_dvd_natCard _ ⟨⟨n, hn⟩, rfl⟩
  have hrange : Nat.card f.range = f.ker.index := (Subgroup.index_ker f).symm
  rw [hrange, hf, normalizerMonoidHom_ker, ← relIndex] at hdvd2
  have hcop : Nat.Coprime (orderOf σ) p := by
    refine Nat.Coprime.coprime_dvd_left hdvd2 ?_
    apply Nat.Coprime.coprime_dvd_left
      (relIndex_dvd_of_le_left _ (le_centralizer (W : Subgroup Y)))
    apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le W.le_normalizer)
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    exact W.not_dvd_index
  have h1 : orderOf σ = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd1
  rw [orderOf_eq_one_iff] at h1
  have hker : (⟨n, hn⟩ : normalizer ((W : Subgroup Y) : Set Y)) ∈ f.ker := MonoidHom.mem_ker.mpr h1
  rw [hf, normalizerMonoidHom_ker, mem_subgroupOf] at hker
  exact hker

theorem mem_ker_transfer_iff (W : Sylow p Y)
    (hNC : normalizer ((W : Subgroup Y) : Set Y) ≤ centralizer ((W : Subgroup Y) : Set Y))
    (y : Y) : y ∈ (MonoidHom.transferSylow W hNC).ker ↔ Nat.Coprime p (orderOf y) := by
  constructor
  · intro hy
    have h1 : orderOf y ∣ Nat.card (MonoidHom.transferSylow W hNC).ker :=
      Subgroup.orderOf_dvd_natCard _ hy
    have h2 := MonoidHom.not_dvd_card_ker_transferSylow W hNC
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    exact fun h => h2 (h.trans h1)
  · intro hy
    rw [MonoidHom.mem_ker]
    set z := MonoidHom.transferSylow W hNC y
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp W.isPGroup' z
    have hzd : orderOf z ∣ orderOf y := orderOf_map_dvd _ y
    rw [hj] at hzd
    have hj0 : j = 0 := by
      by_contra hj0
      have : p ∣ orderOf y := (dvd_pow_self p hj0).trans hzd
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp hy this
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact hj

end Burnside

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_two_normalized {p : ℕ} [Fact p.Prime] {N A : Subgroup G}
    (hN : A ≤ normalizer (N : Set G)) (hA : IsPGroup p A) (hcop : ¬ p ∣ Nat.card N) :
    ∃ S : Subgroup G, S ≤ N ∧ IsPGroup 2 S ∧ (2 ∣ Nat.card N → S ≠ ⊥) ∧
      A ≤ normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction A N := MulDistribMulAction.compHom N (Subgroup.inclusion hN)
  obtain ⟨P₀⟩ := Sylow.nonempty (p := 2) (G := N)
  have hnd : ¬ p ∣ Nat.card (Sylow 2 N) := fun h =>
    hcop (h.trans (P₀.card_dvd_index.trans (P₀ : Subgroup N).index_dvd_card))
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 N) hnd
  have hfwd : ∀ a ∈ A, ∀ g ∈ (P : Subgroup N).map N.subtype,
      a * g * a⁻¹ ∈ (P : Subgroup N).map N.subtype := by
    rintro a ha _ ⟨y, hy, rfl⟩
    have hfix : (⟨a, ha⟩ : A) • P = P := MulAction.mem_fixedPoints.mp hP ⟨a, ha⟩
    have hmem : (⟨a, ha⟩ : A) • y ∈ (⟨a, ha⟩ : A) • (P : Subgroup N) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hy
    have hsub : ((⟨a, ha⟩ : A) • P : Sylow 2 N).toSubgroup =
        (⟨a, ha⟩ : A) • (P : Subgroup N) := Sylow.pointwise_smul_def
    rw [← hsub, hfix] at hmem
    exact ⟨_, hmem, rfl⟩
  refine ⟨(P : Subgroup N).map N.subtype, map_subtype_le _, P.isPGroup'.map _, ?_, ?_⟩
  · intro h2 hbot
    exact P.ne_bot_of_dvd_card h2 ((map_eq_bot_iff_of_injective _ N.subtype_injective).mp hbot)
  · intro a ha
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hfwd a ha g, fun hg => ?_⟩
    have h := hfwd a⁻¹ (A.inv_mem ha) _ hg
    have e : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
    rwa [e] at h

theorem exists_coprimeCore {p : ℕ} [hp : Fact p.Prime] (Y : Subgroup G)
    (hcyc : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S) {x : G} (hxY : x ∈ Y)
    (hx : orderOf x = p) (hxZ : ∀ y ∈ Y, x * y = y * x) :
    ∃ K : Subgroup G, K ≤ Y ∧ ¬ p ∣ Nat.card K ∧
      ∀ g : G, g ∈ K ↔ g ∈ Y ∧ Nat.Coprime p (orderOf g) := by
  obtain ⟨W⟩ := Sylow.nonempty (p := p) (G := Y)
  have hWc : IsCyclic (W : Subgroup Y) := by
    have h := hcyc ((W : Subgroup Y).map Y.subtype) (map_subtype_le _) (W.isPGroup'.map _)
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective (W : Subgroup Y) Y.subtype Y.subtype_injective).symm.surjective
  have hxZ' : (⟨x, hxY⟩ : Y) ∈ center Y := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hxZ y y.2).symm
  have hxo : orderOf (⟨x, hxY⟩ : Y) = p := by rw [Subgroup.orderOf_mk, hx]
  have hxW : (⟨x, hxY⟩ : Y) ∈ (W : Subgroup Y) := by
    have hN : (zpowers (⟨x, hxY⟩ : Y)).Normal :=
      { conj_mem := fun n hn g => by
          have hc : n ∈ center Y := (zpowers_le.mpr hxZ') hn
          rw [(mem_center_iff.mp hc g), mul_inv_cancel_right]
          exact hn }
    have hpg : IsPGroup p (zpowers (⟨x, hxY⟩ : Y)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
    exact hpg.le_sylow_of_normal W (mem_zpowers _)
  have hNC := normalizer_le_centralizer_of_central W hWc hxW hxo hxZ'
  refine ⟨(MonoidHom.transferSylow W hNC).ker.map Y.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact MonoidHom.not_dvd_card_ker_transferSylow W hNC
  · intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      change p.Coprime (orderOf (y : G))
      rw [Subgroup.orderOf_coe]
      exact (mem_ker_transfer_iff W hNC y).mp hy
    · rintro ⟨hgY, hg⟩
      exact ⟨⟨g, hgY⟩,
        (mem_ker_transfer_iff W hNC _).mpr (by rw [Subgroup.orderOf_mk]; exact hg), rfl⟩

end Ambient

end BstarEq

open BstarEq Subgroup

variable {G : Type} [Group G] [Finite G]

theorem bstar_eq_of_twoSub {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hT : ∃ T₀ : Subgroup G, T₀ ≤ centralizer (L : Set G) ∧ T₀ ≤ centralizer ({x} : Set G) ∧
      IsPGroup 2 T₀ ∧ T₀ ≠ ⊥) :
    Bs = B := by
  obtain ⟨hp, hBsE, hxBs, hLx, -⟩ := GGConfig.tableB_facts hC
  haveI := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  have hBBs : B ≤ Bs := hC.2.1.1
  obtain ⟨T₀, hT₀L, hT₀x, hT₀2, hT₀1⟩ := hT
  have hxo : orderOf x = p := orderOf_eq_prime (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hBsx : Bs ≤ centralizer ({x} : Set G) := fun b hb => by
    rw [mem_centralizer_iff]
    rintro _ rfl
    exact TableB.IsElemAbelian.comm hBsE hxBs hb
  have hBsL : Bs ≤ normalizer (L : Set G) := fun b hb => mem_normalizer_of_sstar hS hnc (hBsx hb)
  set Y := centralizer (L : Set G) ⊓ centralizer ({x} : Set G) with hY
  have hxY : x ∈ Y := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro l hl
      have h := mem_centralizer_iff.mp (hLx hl) x rfl
      exact h.symm
    · rw [mem_centralizer_iff]
      rintro _ rfl
      rfl
  have hxZ : ∀ y ∈ Y, x * y = y * x := fun y hy => mem_centralizer_iff.mp hy.2 x rfl
  have hcycY : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S := fun S hSY hpS =>
    hS.2.2.2.2 S (hSY.trans inf_le_left) hpS
  obtain ⟨K, -, hKcop, hKmem⟩ := exists_coprimeCore Y hcycY hxY hxo hxZ
  have hconjY : ∀ b ∈ Bs, ∀ g ∈ Y, b * g * b⁻¹ ∈ Y := by
    intro b hb g hg
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro l hl
      have hl' : b⁻¹ * l * b⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (hBsL hb) _).mpr
        (by rw [show b * (b⁻¹ * l * b⁻¹⁻¹) * b⁻¹ = l by group]; exact hl)
      have hc := mem_centralizer_iff.mp hg.1 _ hl'
      calc l * (b * g * b⁻¹) = b * ((b⁻¹ * l * b⁻¹⁻¹) * g) * b⁻¹ := by group
        _ = b * (g * (b⁻¹ * l * b⁻¹⁻¹)) * b⁻¹ := by rw [hc]
        _ = b * g * b⁻¹ * l := by group
    · rw [mem_centralizer_iff]
      intro h hh
      have hhx : h = x := hh
      rw [hhx]
      have h1 : Commute x g := mem_centralizer_iff.mp hg.2 x rfl
      have h2 : Commute x b := mem_centralizer_iff.mp (hBsx hb) x rfl
      exact ((h2.mul_right h1).mul_right h2.inv_right).eq
  have hconjK : ∀ b ∈ Bs, ∀ g ∈ K, b * g * b⁻¹ ∈ K := by
    intro b hb g hg
    obtain ⟨hgY, hgc⟩ := (hKmem g).mp hg
    refine (hKmem _).mpr ⟨hconjY b hb g hgY, ?_⟩
    have ho : orderOf (b * g * b⁻¹) = orderOf g := by
      have e : (MulAut.conj b) g = b * g * b⁻¹ := MulAut.conj_apply b g
      rw [← e]
      exact orderOf_injective (MulAut.conj b).toMonoidHom (MulAut.conj b).injective g
    rw [ho]
    exact hgc
  have hBsK : Bs ≤ normalizer (K : Set G) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hconjK b hb g, fun hg => ?_⟩
    have h := hconjK b⁻¹ (Bs.inv_mem hb) _ hg
    have e : b⁻¹ * (b * g * b⁻¹) * b⁻¹⁻¹ = g := by group
    rwa [e] at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀K : T₀ ≤ K := by
    intro t ht
    refine (hKmem t).mpr ⟨⟨hT₀L ht, hT₀x ht⟩, ?_⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hT₀2 ⟨t, ht⟩
    have hot : orderOf t = 2 ^ j := by rw [← hj, Subgroup.orderOf_mk]
    rw [hot]
    exact Nat.Coprime.pow_right j ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h2K : 2 ∣ Nat.card K := by
    rcases hT₀2.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.eq_bot_of_card_eq T₀ h1) hT₀1
    · exact h2.trans (Subgroup.card_dvd_of_le hT₀K)
  have hBsP : IsPGroup p Bs := TableB.isPGroup_of_isElemAbelian hBsE
  obtain ⟨S₂, -, hS₂2, hS₂1, hBsS₂⟩ := exists_sylow_two_normalized hBsK hBsP hKcop
  have hS₂ne := hS₂1 h2K
  obtain ⟨e, he⟩ := hBsP.exists_card_eq
  have h1 := CFSG.LargeEvenClassification.Helpers.elementary_pRank_card hp.one_lt Bs hBsE he
  have h2 := CFSG.LargeEvenClassification.Helpers.pRank_mono hp.one_lt hBsS₂
  have h3 := CFSG.LargeEvenClassification.Helpers.pRank_le_twoLocalPRank hp.one_lt _
    (⟨S₂, hS₂ne, hS₂2, rfl⟩ : CFSG.Open.IsTwoLocal (normalizer (S₂ : Set G)))
  rw [h1] at h2
  have hle : e ≤ LargeEvenTwoLocalRank p G := h2.trans h3
  have hcardB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hS.1.2.1
  have hcard : Nat.card Bs ≤ Nat.card B := by
    rw [he, hcardB]
    exact Nat.pow_le_pow_right hp.pos hle
  exact (Subgroup.eq_of_le_of_card_ge hBBs hcard).symm

theorem bstar_eq_of_moved {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hT : ∃ T₀ : Subgroup G, T₀ ≤ centralizer (L : Set G) ∧ T₀ ≤ centralizer ({x} : Set G) ∧
      IsPGroup 2 T₀ ∧ B ≤ normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥) :
    Bs = B := by
  obtain ⟨T₀, hT₀L, hT₀x, hT₀2, -, hT₀B⟩ := hT
  refine bstar_eq_of_twoSub hC hnc ⟨T₀, hT₀L, hT₀x, hT₀2, ?_⟩
  rintro rfl
  exact hT₀B (Subgroup.commutator_bot_left B)

theorem GGConfig.twoSub_centralizer_eq_bot {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hne : B ≠ Bs)
    {T₀ : Subgroup G} (hTL : T₀ ≤ centralizer (L : Set G))
    (hTx : T₀ ≤ centralizer ({x} : Set G)) (hT2 : IsPGroup 2 T₀) : T₀ = ⊥ := by
  by_contra h1
  exact hne (bstar_eq_of_twoSub hC hnc ⟨T₀, hTL, hTx, hT2, h1⟩).symm

theorem ggInnerDiagOnLab_bstar_of_moved {S : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hM : GGInnerDiagOnLab S p B L)
    (hT : ∃ T₀ : Subgroup G, T₀ ≤ centralizer (L : Set G) ∧ T₀ ≤ centralizer ({x} : Set G) ∧
      IsPGroup 2 T₀ ∧ B ≤ normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥) :
    GGInnerDiagOnLab S p Bs L := by
  rw [bstar_eq_of_moved hC hnc hT]
  exact hM

end CFSG.StandardType
