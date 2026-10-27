module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34AutE8
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.Goldschmidt.Steps.G3b35Basic
import CFSG.Goldschmidt.Steps.G76U34
import CFSG.Adapters.GeneralizedFitting
import CFSG.CGT.Timmesfeld75.ListWCSzU3
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.Goldschmidt.Steps.G3bPSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.GH74.Uniqueness.Bender
open CFSG.Goldschmidt.G3b (conjQuot conjQuot_mk conjQuot_of_mem conjQuot_eq_one_iff)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem u34aute8_centralizer_le_iSup {Y : Type} [Group Y] {A : Subgroup Y} {a : Y}
    (ha : a ∈ A) (ha1 : a ≠ 1) :
    centralizer ({a} : Set Y) ≤ ⨆ b ∈ A, ⨆ (_ : b ≠ 1), centralizer ({b} : Set Y) :=
  le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)

theorem u34aute8_odd_card_center {Y : Type} [Group Y] [Finite Y] (F : Subgroup Y)
    (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1) :
    Odd (Nat.card (center ↥F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : (z : ↥F) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hz, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  have hz1 : z = 1 := Subtype.ext (hZ2 z z.2 1 hz2)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem u34aute8_eq_one_of_mem_centralizer {Y : Type} [Group Y] (F : Subgroup Y)
    (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hCF : centralizer (F : Set Y) ≤ F) {a : Y} (ha : a ^ 2 = 1)
    (haC : a ∈ centralizer (F : Set Y)) : a = 1 := by
  have haF : a ∈ F := hCF haC
  have hz : (⟨a, haF⟩ : ↥F) ∈ center ↥F := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp haC g g.2)
  have h1 := hZ2 _ hz 1 (Subtype.ext (by simpa using ha))
  simpa using congrArg Subtype.val h1

theorem u34aute8_mem_of_conjQuot_mem_inner {Y : Type} [Group Y] (F : Subgroup Y) [F.Normal]
    (hperf : commutator ↥F = ⊤) (hCF : centralizer (F : Set Y) ≤ F) {y : Y}
    (hy : conjQuot F y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (↥F ⧸ center ↥F)) :
    y ∈ F := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
  have h := CFSG.Goldschmidt.G3b.mem_sup_centralizer_of_conjQuot_eq_conj F hperf l hk.symm
  rwa [sup_eq_left.mpr hCF] at h

theorem u34aute8_conjQuot_mem_inner {Y : Type} [Group Y] (F : Subgroup Y) [F.Normal] {y : Y}
    (hy : y ∈ F) :
    conjQuot F y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (↥F ⧸ center ↥F) :=
  ⟨_, (conjQuot_of_mem F hy).symm⟩

theorem u34aute8_conjQuot_injOn {Y : Type} [Group Y] (F : Subgroup Y) [F.Normal]
    (hperf : commutator ↥F = ⊤) (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hCF : centralizer (F : Set Y) ≤ F) {A : Subgroup Y} (hA : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ s ∈ A, ∀ t ∈ A, conjQuot F s = conjQuot F t → s = t := by
  intro s hs t ht hst
  have h1 : conjQuot F (s⁻¹ * t) = 1 := by rw [map_mul, map_inv, hst, inv_mul_cancel]
  rw [conjQuot_eq_one_iff F hperf] at h1
  exact inv_mul_eq_one.mp
    (u34aute8_eq_one_of_mem_centralizer F hZ2 hCF (hA _ (A.mul_mem (A.inv_mem hs) ht)) h1)

theorem u34aute8_exists_lift {Y : Type} [Group Y] [Finite Y] (F : Subgroup Y) [F.Normal]
    (hZodd : Odd (Nat.card (center ↥F))) {τ : Y} (hτ : τ * τ = 1)
    (xb : ↥F ⧸ center ↥F) (hxb : conjQuot F τ xb = xb) :
    ∃ x : ↥F, (x : ↥F ⧸ center ↥F) = xb ∧ τ * (x : Y) * τ⁻¹ = x := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  have hc : ∀ f : ↥F, ((MulAut.conjNormal τ f : ↥F) : Y) = τ * f * τ⁻¹ :=
    fun f => MulAut.conjNormal_apply τ f
  have hcc : ∀ f : ↥F, MulAut.conjNormal τ (MulAut.conjNormal τ f) = f := by
    intro f
    apply Subtype.ext
    rw [hc, hc]
    calc τ * (τ * (f : Y) * τ⁻¹) * τ⁻¹ = (τ * τ) * f * (τ * τ)⁻¹ := by group
      _ = f := by rw [hτ]; group
  have hcZ : ∀ z ∈ center ↥F, MulAut.conjNormal τ z ∈ center ↥F := by
    intro z hz
    rw [← CFSG.Goldschmidt.G3b.center_map_conjNormal F τ]
    exact ⟨z, hz, rfl⟩
  have h0 : x₀⁻¹ * MulAut.conjNormal τ x₀ ∈ center ↥F := by
    have h1 := hxb
    rw [conjQuot_mk] at h1
    have h2 : ((MulAut.conjNormal τ x₀ : ↥F) : ↥F ⧸ center ↥F) = x₀ := by
      rw [← h1]
      exact congrArg _ (Subtype.ext (hc x₀))
    have h4 := (center ↥F).inv_mem (QuotientGroup.eq.mp h2)
    rwa [mul_inv_rev, inv_inv] at h4
  let g : center ↥F → center ↥F := fun z => ⟨x₀⁻¹ * MulAut.conjNormal τ (x₀ * (z : ↥F)), by
    rw [map_mul, ← mul_assoc]
    exact (center ↥F).mul_mem h0 (hcZ z z.2)⟩
  have hg : Function.Involutive g := by
    intro z
    apply Subtype.ext
    change x₀⁻¹ * MulAut.conjNormal τ (x₀ * (x₀⁻¹ * MulAut.conjNormal τ (x₀ * (z : ↥F)))) = z
    rw [mul_inv_cancel_left, hcc, inv_mul_cancel_left]
  obtain ⟨z, hz⟩ := exists_fixed_of_odd_card g hg hZodd
  have hz' : MulAut.conjNormal τ (x₀ * (z : ↥F)) = x₀ * z := by
    have h1 : x₀⁻¹ * MulAut.conjNormal τ (x₀ * (z : ↥F)) = z := congrArg Subtype.val hz
    calc MulAut.conjNormal τ (x₀ * (z : ↥F))
        = x₀ * (x₀⁻¹ * MulAut.conjNormal τ (x₀ * (z : ↥F))) := by group
      _ = x₀ * z := by rw [h1]
  refine ⟨x₀ * (z : ↥F), ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (z : ↥F)).mpr z.2, mul_one]
  · rw [← hc (x₀ * (z : ↥F)), hz']

theorem u34aute8_fixed_psl2 {Y : Type} [Group Y] (F : Subgroup Y) [F.Normal]
    (hperf : commutator ↥F = ⊤) (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ}
    (hB : BenderType (↥F ⧸ center ↥F) 2 3 e) {τ : Y} (hτ : τ * τ = 1) (hτF : τ ∉ F) :
    Nonempty (autFixed (conjQuot F τ) ≃* CFSG.Theory.Comparator.PSL2Model 2) := by
  refine hB.fixed_unitary (conjQuot F τ) (by rw [← map_mul, hτ, map_one]) ?_
  rintro ⟨g, hg⟩
  apply hτF
  apply u34aute8_mem_of_conjQuot_mem_inner F hperf hCF
  exact ⟨g, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hg x]⟩

theorem u34aute8_exists_three {Y : Type} [Group Y] [Finite Y] (F : Subgroup Y) [F.Normal]
    (hperf : commutator ↥F = ⊤) (hZodd : Odd (Nat.card (center ↥F)))
    (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e)
    {τ : Y} (hτ : τ * τ = 1) (hτF : τ ∉ F) :
    ∃ x : ↥F, τ * (x : Y) * τ⁻¹ = x ∧ 3 ∣ orderOf x := by
  obtain ⟨φ⟩ := u34aute8_fixed_psl2 F hperf hCF hB hτ hτF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (autFixed (conjQuot F τ)) = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact (card_psl2_even 2 (by norm_num)).trans (by norm_num)
  obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := autFixed (conjQuot F τ)) 3
    (by rw [hcard]; norm_num)
  obtain ⟨x, hx, hxτ⟩ := u34aute8_exists_lift F hZodd hτ (xb : ↥F ⧸ center ↥F) xb.2
  refine ⟨x, hxτ, ?_⟩
  have h1 := orderOf_map_dvd (QuotientGroup.mk' (center ↥F)) x
  rw [QuotientGroup.mk'_apply, hx, Subgroup.orderOf_coe, hxb] at h1
  exact h1

theorem u34aute8_le_normalClosure {Y : Type} [Group Y] (F : Subgroup Y)
    (hq : CFSG.Open.IsQuasisimple ↥F) (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    {A : Subgroup Y} (hA : ∀ a ∈ A, a ^ 2 = 1) {a : Y} (haA : a ∈ A) (haF : a ∈ F)
    (ha1 : a ≠ 1) : F ≤ normalClosure (A : Set Y) := by
  have hN : ((normalClosure (A : Set Y)).subgroupOf F).Normal :=
    Subgroup.Normal.subgroupOf normalClosure_normal F
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    ((normalClosure (A : Set Y)).subgroupOf F) with h | h
  · exfalso
    have hmem : (⟨a, haF⟩ : ↥F) ∈ (normalClosure (A : Set Y)).subgroupOf F :=
      mem_subgroupOf.mpr (subset_normalClosure haA)
    exact ha1 (congrArg Subtype.val
      (hZ2 _ (h hmem) 1 (Subtype.ext (by simpa using hA a haA))))
  · intro x hx
    have : (⟨x, hx⟩ : ↥F) ∈ (normalClosure (A : Set Y)).subgroupOf F := h ▸ mem_top _
    exact mem_subgroupOf.mp this

theorem u34aute8_three_dvd {Y : Type} [Group Y] [Finite Y] (F : Subgroup Y) [F.Normal]
    (hperf : commutator ↥F = ⊤) (hZodd : Odd (Nat.card (center ↥F)))
    (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e)
    {A : Subgroup Y} (hFA : F ≤ normalClosure (A : Set Y)) {τ : Y} (hτ : τ * τ = 1)
    (hτF : τ ∉ F) :
    3 ∣ Nat.card ↥(normalClosure (A : Set Y) ⊓ centralizer ({τ} : Set Y)) := by
  obtain ⟨x, hxτ, h3⟩ := u34aute8_exists_three F hperf hZodd hCF hB hτ hτF
  have hxC : (x : Y) ∈ centralizer ({τ} : Set Y) := by
    rw [mem_centralizer_singleton_iff]
    calc (x : Y) * τ = (τ * x * τ⁻¹) * τ := by rw [hxτ]
      _ = τ * x := by group
  have hmem : (x : Y) ∈ normalClosure (A : Set Y) ⊓ centralizer ({τ} : Set Y) :=
    ⟨hFA x.2, hxC⟩
  have h := orderOf_dvd_natCard
    (⟨x, hmem⟩ : ↥(normalClosure (A : Set Y) ⊓ centralizer ({τ} : Set Y)))
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h
  exact h3.trans h

theorem u34aute8_isPGroup_outer {K : Type*} [Group K] {e : ℕ} (hB : BenderType K 2 3 e) :
    IsPGroup 2 (Outer K) := by
  obtain ⟨Dd, hn, -, hd, -, hq⟩ := hB.outer_unitary
  have := hn
  refine IsPGroup.of_card (n := 2) ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Dd, hq, hd]
  norm_num

theorem u34aute8_isPGroup_quotient {Y : Type} [Group Y] (F : Subgroup Y) [F.Normal]
    (hperf : commutator ↥F = ⊤) (hCF : centralizer (F : Set Y) ≤ F)
    (hOut : IsPGroup 2 (Outer (↥F ⧸ center ↥F))) : IsPGroup 2 (Y ⧸ F) := by
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨k, hk⟩ := hOut (QuotientGroup.mk
    (s := CFSG.ComponentClassification.OuterAutomorphisms.inner (↥F ⧸ center ↥F)) (conjQuot F y))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply u34aute8_mem_of_conjQuot_mem_inner F hperf hCF
  rw [map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact hk

section Certified

theorem u34aute8_card_le_eight {Y : Type} [Group Y] [Finite Y]
    (F : Subgroup Y) [F.Normal] (hperf : commutator ↥F = ⊤)
    (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e)
    {A : Subgroup Y} (hA : ∀ a ∈ A, a ^ 2 = 1) : Nat.card A ≤ 8 := by
  have h := (hB.card_le_of_sq_eq_one_aut (A.map (conjQuot F)) ?_).1
  · rw [CFSG.Goldschmidt.G76.card_map_eq_of_injOn _
      (u34aute8_conjQuot_injOn F hperf hZ2 hCF hA)] at h
    norm_num at h
    exact h
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← sq, hA a ha, map_one]

theorem u34aute8_card_subgroupOf_le_four {Y : Type} [Group Y]
    [Finite Y] (F : Subgroup Y) (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e) {A : Subgroup Y}
    (hA : ∀ a ∈ A, a ^ 2 = 1) : Nat.card (A.subgroupOf F) ≤ 4 := by
  have hinj : ∀ s ∈ A.subgroupOf F, ∀ t ∈ A.subgroupOf F,
      QuotientGroup.mk' (center ↥F) s = QuotientGroup.mk' (center ↥F) t → s = t := by
    intro s hs t ht hst
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
    have hst' : s⁻¹ * t ∈ A.subgroupOf F :=
      (A.subgroupOf F).mul_mem ((A.subgroupOf F).inv_mem hs) ht
    have h2 : (s⁻¹ * t) ^ 2 ^ 1 = 1 := Subtype.ext (by simpa using hA _ hst')
    exact inv_mul_eq_one.mp (hZ2 _ hst 1 h2)
  have h := hB.card_le_of_sq_eq_one ((A.subgroupOf F).map (QuotientGroup.mk' (center ↥F))) ?_
  · rw [CFSG.Goldschmidt.G76.card_map_eq_of_injOn _ hinj] at h
    norm_num at h
    exact h
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by simpa [sq] using hA _ hx)
    rw [this, map_one]

theorem u34aute8_card_le_two_mul {Y : Type} [Group Y] [Finite Y]
    (F : Subgroup Y) [F.Normal] (hperf : commutator ↥F = ⊤)
    (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e)
    {A : Subgroup Y} (hA : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ 2 * Nat.card (A.subgroupOf F) := by
  set f : A →* Outer (↥F ⧸ center ↥F) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (↥F ⧸ center ↥F))).comp ((conjQuot F).comp A.subtype) with hf
  have hker : f.ker = F.subgroupOf A := by
    ext x
    simp only [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨u34aute8_mem_of_conjQuot_mem_inner F hperf hCF, u34aute8_conjQuot_mem_inner F⟩
  have hcard : Nat.card A = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hrange : Nat.card f.range ≤ 2 := by
    have hsqr : ∀ r ∈ f.range, r * r = 1 := by
      rintro _ ⟨x, rfl⟩
      rw [← map_mul]
      have : (x * x : A) = 1 := Subtype.ext (by simpa [sq] using hA x x.2)
      rw [this, map_one]
    have hp : IsPGroup 2 f.range := isPGroup_two_of_mul_self_eq_one hsqr
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    have hcyc : IsCyclic S := hB.isCyclic_sylow_outer S
    have hcycR : IsCyclic f.range :=
      isCyclic_of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := f.range)
    have hog : orderOf g = Nat.card f.range := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg2 : g ^ 2 = 1 := by
      have := hsqr g g.2
      exact Subtype.ext (by simpa [sq] using this)
    rw [← hog]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  have hcomm : Nat.card (F.subgroupOf A) = Nat.card (A.subgroupOf F) := by
    rw [← inf_subgroupOf_right F A, ← inf_subgroupOf_right A F,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : F ⊓ A ≤ A)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : A ⊓ F ≤ F)).toEquiv, inf_comm]
  rw [hcard, hker, hcomm]
  exact Nat.mul_le_mul_right _ hrange

theorem u34aute8_exists_fixed_not_mem_borel {Y : Type} [Group Y]
    [Finite Y] (F : Subgroup Y) [F.Normal] (hperf : commutator ↥F = ⊤)
    (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e)
    {τ : Y} (hτ : τ * τ = 1) (hτF : τ ∉ F) (Q : Sylow 2 (↥F ⧸ center ↥F)) :
    ∃ xb ∈ autFixed (conjQuot F τ), xb ∉ borel (Q : Subgroup (↥F ⧸ center ↥F)) := by
  obtain ⟨φ⟩ := u34aute8_fixed_psl2 F hperf hCF hB hτ hτF
  by_contra hcon
  have hle : autFixed (conjQuot F τ) ≤ borel (Q : Subgroup (↥F ⧸ center ↥F)) := by
    intro x hx
    by_contra hxB
    exact hcon ⟨x, hx, hxB⟩
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  have : Group.IsSolvable (borel (Q : Subgroup (↥F ⧸ center ↥F))) := hc.isSolvable_borel
  have : Group.IsSolvable (autFixed (conjQuot F τ)) := isSolvable_of_le_isSolvable hle
  exact BenderType.not_solvable_of_psl2 (le_refl 2) φ this

theorem u34aute8_le_iSup {Y : Type} [Group Y] [Finite Y]
    (F : Subgroup Y) [F.Normal] (hq : CFSG.Open.IsQuasisimple ↥F)
    (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e)
    {A : Subgroup Y} (hA : ∀ a ∈ A, a ^ 2 = 1) {a : Y} (haA : a ∈ A) (haF : a ∈ F)
    (ha1 : a ≠ 1) {τ : Y} (hτA : τ ∈ A) (hτF : τ ∉ F) :
    F ≤ ⨆ b ∈ A, ⨆ (_ : b ≠ 1), centralizer ({b} : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (↥F ⧸ center ↥F) := hq.2
  have hZodd := u34aute8_odd_card_center F hZ2
  have ha2 : a * a = 1 := by rw [← sq]; exact hA a haA
  have hτ2 : τ * τ = 1 := by rw [← sq]; exact hA τ hτA
  have hτ1 : τ ≠ 1 := fun h => hτF (h ▸ F.one_mem)
  set H := ⨆ b ∈ A, ⨆ (_ : b ≠ 1), centralizer ({b} : Set Y) with hH
  suffices hM : H.subgroupOf F = ⊤ by
    intro x hx
    have : (⟨x, hx⟩ : ↥F) ∈ H.subgroupOf F := hM ▸ mem_top _
    exact this
  apply CFSG.Walter.eq_top_of_sup_center_eq_top hq.1
  set ab : ↥F ⧸ center ↥F := ((⟨a, haF⟩ : ↥F) : ↥F ⧸ center ↥F) with hab
  have hab1 : ab ≠ 1 := by
    intro h
    rw [hab, QuotientGroup.eq_one_iff] at h
    exact ha1 (congrArg Subtype.val (hZ2 _ h 1 (Subtype.ext (by simpa using hA a haA))))
  have hab2 : ab * ab = 1 := by
    rw [hab, ← QuotientGroup.mk_mul]
    have : (⟨a, haF⟩ : ↥F) * ⟨a, haF⟩ = 1 := Subtype.ext ha2
    rw [this, QuotientGroup.mk_one]
  have hzp : IsPGroup 2 (zpowers ab) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact hab2) hab1)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  have habZ := hc.mem_rootCenter_of_mul_self (hQ (mem_zpowers ab)) hab2
  have hQM : (Q : Subgroup (↥F ⧸ center ↥F)) ≤
      (H.subgroupOf F).map (QuotientGroup.mk' (center ↥F)) := by
    intro qb hqb
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (center ↥F) qb
    refine ⟨q, ?_, rfl⟩
    have hqC : (q : Y) ∈ centralizer ({a} : Set Y) := by
      rw [CFSG.Walter.mem_centralizer_iff_of_inner hZodd ha2 haF (fun _ _ => rfl) q,
        mem_centralizer_singleton_iff]
      exact (mem_rootCenter_iff.mp habZ).2 _ hqb
    exact mem_subgroupOf.mpr (u34aute8_centralizer_le_iSup haA ha1 hqC)
  obtain ⟨xb, hxb, hxbB⟩ := u34aute8_exists_fixed_not_mem_borel F hq.1 hCF hB hτ2 hτF Q
  obtain ⟨x, hx, hxτ⟩ := u34aute8_exists_lift F hZodd hτ2 xb hxb
  have hxC : (x : Y) ∈ centralizer ({τ} : Set Y) := by
    rw [mem_centralizer_singleton_iff]
    calc (x : Y) * τ = (τ * x * τ⁻¹) * τ := by rw [hxτ]
      _ = τ * x := by group
  have hxM : x ∈ H.subgroupOf F :=
    mem_subgroupOf.mpr (u34aute8_centralizer_le_iSup hτA hτ1 hxC)
  have hmap : (H.subgroupOf F).map (QuotientGroup.mk' (center ↥F)) = ⊤ := by
    rw [eq_top_iff, ← hc.sup_zpowers_eq_top hxbB]
    refine sup_le hQM (zpowers_le.mpr ⟨x, hxM, ?_⟩)
    rw [QuotientGroup.mk'_apply, hx]
  have h := Subgroup.comap_map_eq (QuotientGroup.mk' (center ↥F)) (H.subgroupOf F)
  rw [hmap, comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

theorem u34aute8_conj_mem {Y : Type} [Group Y] [Finite Y]
    (F : Subgroup Y) [F.Normal] (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e) {A : Subgroup Y}
    (hA : ∀ a ∈ A, a ^ 2 = 1) (hAF : Nat.card (A.subgroupOf F) = 4) {S : Subgroup Y}
    (hS : IsPGroup 2 S) (hAS : A ≤ S) {s v : Y} (hs : s ∈ S) (hvA : v ∈ A) (hvF : v ∈ F) :
    s * v * s⁻¹ ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPS : IsPGroup 2 (S.subgroupOf F) := hS.comap_subtype
  obtain ⟨Q, hQ⟩ := (hPS.map (QuotientGroup.mk' (center ↥F))).exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  have hAS' : A.subgroupOf F ≤ S.subgroupOf F := fun x hx => hAS hx
  have hinj : ∀ x ∈ S.subgroupOf F, ∀ y ∈ S.subgroupOf F,
      QuotientGroup.mk' (center ↥F) x = QuotientGroup.mk' (center ↥F) y → x = y := by
    intro x hx y hy hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
    obtain ⟨k, hk⟩ := hPS ⟨x⁻¹ * y, (S.subgroupOf F).mul_mem ((S.subgroupOf F).inv_mem hx) hy⟩
    exact inv_mul_eq_one.mp (hZ2 _ hxy k (by simpa using congrArg Subtype.val hk))
  have hVZ : (A.subgroupOf F).map (QuotientGroup.mk' (center ↥F)) =
      rootCenter (Q : Subgroup (↥F ⧸ center ↥F)) := by
    refine Subgroup.eq_of_le_of_card_ge (hc.elemAbelian_le_rootCenter
      ((map_mono hAS').trans hQ) ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have : x * x = 1 := Subtype.ext (by simpa [sq] using hA _ hx)
      rw [this, map_one]
    · rw [hc.card_center, CFSG.Goldschmidt.G76.card_map_eq_of_injOn _
        (fun x hx y hy => hinj x (hAS' hx) y (hAS' hy)), hAF]
      norm_num
  have hwF : s * v * s⁻¹ ∈ F := (inferInstance : F.Normal).conj_mem v hvF s
  have hwS : s * v * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs (hAS hvA)) (S.inv_mem hs)
  have hw2 : (⟨s * v * s⁻¹, hwF⟩ : ↥F) * ⟨s * v * s⁻¹, hwF⟩ = 1 := by
    apply Subtype.ext
    have hv2 : v * v = 1 := by rw [← sq]; exact hA v hvA
    change s * v * s⁻¹ * (s * v * s⁻¹) = 1
    calc s * v * s⁻¹ * (s * v * s⁻¹) = s * (v * v) * s⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hwQ : QuotientGroup.mk' (center ↥F) ⟨s * v * s⁻¹, hwF⟩ ∈
      (Q : Subgroup (↥F ⧸ center ↥F)) := hQ ⟨⟨s * v * s⁻¹, hwF⟩, hwS, rfl⟩
  have hwZ := hc.mem_rootCenter_of_mul_self hwQ (by rw [← map_mul, hw2, map_one])
  rw [← hVZ] at hwZ
  obtain ⟨v', hv'A, hv'w⟩ := hwZ
  have h := hinj v' (hAS' hv'A) ⟨s * v * s⁻¹, hwF⟩ hwS hv'w
  subst h
  exact hv'A

theorem u34aute8_iSup_eq_top {Y : Type} [Group Y] [Finite Y]
    (F : Subgroup Y) [F.Normal] (hperf : commutator ↥F = ⊤)
    (hZ2 : ∀ z ∈ center ↥F, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hCF : centralizer (F : Set Y) ≤ F) {e : ℕ} (hB : BenderType (↥F ⧸ center ↥F) 2 3 e)
    {A : Subgroup Y} (hA : ∀ a ∈ A, a ^ 2 = 1) (hAF : Nat.card (A.subgroupOf F) = 4)
    (hFH : F ≤ ⨆ b ∈ A, ⨆ (_ : b ≠ 1), centralizer ({b} : Set Y)) :
    (⨆ b ∈ A, ⨆ (_ : b ≠ 1), centralizer ({b} : Set Y)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY := u34aute8_isPGroup_quotient F hperf hCF (u34aute8_isPGroup_outer hB)
  have hA' : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA a ha
  obtain ⟨S, hAS⟩ := (isPGroup_two_of_mul_self_eq_one hA').exists_le_sylow
  have hSF : (S : Subgroup Y) ⊔ F = ⊤ := CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top hY S
  have hN : (S : Subgroup Y) ≤ normalizer ((A ⊓ F : Subgroup Y) : Set Y) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro v
    constructor
    · rintro ⟨hvA, hvF⟩
      exact ⟨u34aute8_conj_mem F hZ2 hB hA hAF S.isPGroup' hAS hs hvA hvF,
        (inferInstance : F.Normal).conj_mem v hvF s⟩
    · rintro ⟨hwA, hwF⟩
      have e1 : s⁻¹ * (s * v * s⁻¹) * s⁻¹⁻¹ = v := by group
      have hvF : v ∈ F := by
        have := (inferInstance : F.Normal).conj_mem _ hwF s⁻¹
        rwa [e1] at this
      have := u34aute8_conj_mem F hZ2 hB hA hAF S.isPGroup' hAS (S.inv_mem hs) hwA hwF
      rw [e1] at this
      exact ⟨this, hvF⟩
  have hne : A ⊓ F ≠ ⊥ := by
    intro h
    rw [← inf_subgroupOf_right, h, bot_subgroupOf, card_bot] at hAF
    omega
  obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (CFSG.QuasithinUnique.inf_centralizer_ne_bot_of_normalizes S.isPGroup'
      (inf_le_left.trans hAS) hN hne)
  have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  have hSle : (S : Subgroup Y) ≤ centralizer ({a₀} : Set Y) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp ha₀.2 s hs
  rw [eq_top_iff, ← hSF]
  exact sup_le (hSle.trans (u34aute8_centralizer_le_iSup ha₀.1.1 ha₀1')) hFH

theorem k_U34AutE8_holds : K_U34AutE8 := by
  intro Y _ _ hq hL A hA hA8
  have : (genFittingFStar Y).Normal := CFSG.ComponentClassification.GeneralizedFitting.normal Y
  have hCF := CFSG.Adapters.generalized_fitting_self_centralizing Y
  obtain ⟨eU⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel le_rfl
    (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide))
  have hB : BenderType (↥(genFittingFStar Y) ⧸ center ↥(genFittingFStar Y)) 2 3
      ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) :=
    BenderType.unitary 2 le_rfl (eU.trans (MulEquiv.subgroupCongr
      (show CFSG.Open.PSU3 2 2 = CFSG.Theory.Comparator.PSU3Model 2 from rfl)))
  have hZ2 := CFSG.Goldschmidt.G76.center_two_eq_one_of_psu3 hq eU
  have hZodd := u34aute8_odd_card_center _ hZ2
  have hperf : commutator ↥(genFittingFStar Y) = ⊤ := hq.1
  have h8 : Nat.card A = 8 :=
    le_antisymm (u34aute8_card_le_eight _ hperf hZ2 hCF hB hA) hA8
  have h4 : Nat.card (A.subgroupOf (genFittingFStar Y)) = 4 := by
    have h1 := u34aute8_card_subgroupOf_le_four _ hZ2 hB hA
    have h2 := u34aute8_card_le_two_mul _ hperf hCF hB hA
    omega
  obtain ⟨τ, hτA, hτF⟩ : ∃ τ ∈ A, τ ∉ genFittingFStar Y := by
    by_contra hcon
    have hle : A ≤ genFittingFStar Y := fun x hx => by
      by_contra hxF
      exact hcon ⟨x, hx, hxF⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, h8] at h4
    omega
  obtain ⟨a, haA, haF, ha1⟩ : ∃ a ∈ A, a ∈ genFittingFStar Y ∧ a ≠ 1 := by
    have hne : A.subgroupOf (genFittingFStar Y) ≠ ⊥ := by
      intro h
      rw [h, card_bot] at h4
      omega
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨x, hx, x.2, fun h => hx1 (Subtype.ext (Subtype.ext h))⟩
  have hτ1 : τ ≠ 1 := fun h => hτF (h ▸ (genFittingFStar Y).one_mem)
  have hτ2 : τ * τ = 1 := by rw [← sq]; exact hA τ hτA
  have hFH := u34aute8_le_iSup _ hq hZ2 hCF hB hA haA haF ha1 hτA hτF
  exact ⟨h8, u34aute8_iSup_eq_top _ hperf hZ2 hCF hB hA h4 hFH, τ, hτA, hτ1,
    u34aute8_three_dvd _ hperf hZodd hCF hB
      (u34aute8_le_normalClosure _ hq hZ2 hA haA haF ha1) hτ2 hτF⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
