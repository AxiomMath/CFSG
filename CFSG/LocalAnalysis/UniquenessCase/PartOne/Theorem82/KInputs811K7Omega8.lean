module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6aHolds
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeD
import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup CFSG.Open CFSG.LieType.BorelTits

@[expose] def K7bOmega8Clause {Y : Type*} [Group Y] (A : Subgroup Y) (p : ℕ) : Prop :=
  ∃ y ∈ centralizer (A : Set Y), orderOf y = p ∧ ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
    ∃ u ∈ centralizer (X : Set Y), orderOf u = p ∧ u * y = y * u ∧ u ∉ zpowers y

theorem K7bOmega8Clause.map_of_injective {Y Y' : Type*} [Group Y] [Group Y']
    {A : Subgroup Y} {p : ℕ} (φ : Y →* Y') (hφ : Function.Injective φ)
    (h : K7bOmega8Clause A p) : K7bOmega8Clause (A.map φ) p := by
  obtain ⟨y, hyA, hyord, hX⟩ := h
  refine ⟨φ y, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff] at hyA ⊢
    intro a' ha'
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [← map_mul, ← map_mul, hyA a haA]
  · exact (orderOf_injective φ hφ y).trans hyord
  · intro X' hX'A hX'card
    let X : Subgroup Y := X'.comap φ ⊓ A
    have hXA : X ≤ A := inf_le_right
    have hXmap : X.map φ = X' := by
      refine le_antisymm ?_ ?_
      · intro x' hx'
        obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hx'
        exact Subgroup.mem_comap.mp hxX.1
      · intro x' hx'
        obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp (hX'A hx')
        exact Subgroup.mem_map.mpr ⟨a, ⟨Subgroup.mem_comap.mpr hx', haA⟩, rfl⟩
    have hXcard : Nat.card X = 3 := by
      rw [← Subgroup.card_map_of_injective hφ, hXmap, hX'card]
    obtain ⟨u, huC, huord, huy, hunot⟩ := hX X hXA hXcard
    refine ⟨φ u, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at huC ⊢
      intro x' hx'
      rw [← hXmap] at hx'
      obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hx'
      rw [← map_mul, ← map_mul, huC x hxX]
    · exact (orderOf_injective φ hφ u).trans huord
    · rw [← map_mul, ← map_mul, huy]
    · intro hmem
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      apply hunot
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, hφ (by rw [map_zpow, hk])⟩

private theorem orderOf_mk_eq_prime_of_sq_eq_one {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal]
    (hN2 : ∀ n ∈ N, n ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : Y}
    (hx : orderOf x = p) : orderOf (QuotientGroup.mk' N x) = p := by
  have hdvd : orderOf (QuotientGroup.mk' N x) ∣ p := hx ▸ orderOf_map_dvd _ x
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exfalso
    have hxN : x ∈ N := QuotientGroup.eq_one_iff x |>.mp (orderOf_eq_one_iff.mp h1)
    have h2 : x ^ 2 = 1 := hN2 x hxN
    have hp2dvd : p ∣ 2 := hx ▸ orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2dvd with h | h
    · exact hp.one_lt.ne' h
    · exact hp2 h
  · exact hp'

theorem K7bOmega8Clause.map_mk {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal]
    {A : Subgroup Y} {p : ℕ} (hN2 : ∀ n ∈ N, n ^ 2 = 1) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (h : K7bOmega8Clause A p) :
    K7bOmega8Clause (A.map (QuotientGroup.mk' N)) p := by
  obtain ⟨y, hyA, hyord, hX⟩ := h
  refine ⟨QuotientGroup.mk' N y, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff] at hyA ⊢
    intro a' ha'
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [← map_mul, ← map_mul, hyA a haA]
  · exact orderOf_mk_eq_prime_of_sq_eq_one hN2 hp hp2 hyord
  · intro X' hX'A hX'card
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Finite X' := (Nat.card_ne_zero.mp (by rw [hX'card]; norm_num)).2
    obtain ⟨x', hx'ord⟩ := exists_prime_orderOf_dvd_card' (G := X') 3 (by rw [hX'card])
    have hx'ordq : orderOf (x' : Y ⧸ N) = 3 := by
      simpa using (Subgroup.orderOf_coe x').trans hx'ord
    have hx'ne : (x' : Y ⧸ N) ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hx'ordq
      omega
    obtain ⟨a, haA, hax⟩ := Subgroup.mem_map.mp (hX'A x'.2)
    have ha_ne : a ≠ 1 := fun h1 => hx'ne (by rw [← hax, h1, map_one])
    have haord : orderOf a = 3 := orderOf_eq_prime (hA3 a haA) ha_ne
    have hXcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, haord]
    obtain ⟨u, huC, huord, huy, hunot⟩ :=
      hX (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA) hXcard
    have hX'eq : X' = Subgroup.zpowers (x' : Y ⧸ N) :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x'.2)
        (by rw [hX'card, Nat.card_zpowers, hx'ordq])).symm
    refine ⟨QuotientGroup.mk' N u, ?_, ?_, ?_, ?_⟩
    · rw [hX'eq, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hw' : w = QuotientGroup.mk' N (a ^ k) :=
        hk.symm.trans (by rw [← hax, map_zpow])
      rw [hw', ← map_mul, ← map_mul,
        huC (a ^ k) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)]
    · exact orderOf_mk_eq_prime_of_sq_eq_one hN2 hp hp2 huord
    · rw [← map_mul, ← map_mul, huy]
    · intro hmem
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      have hzN : QuotientGroup.mk' N (u * (y ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, ← hk]
        exact mul_inv_cancel _
      have hz : u * (y ^ k)⁻¹ ∈ N := (QuotientGroup.eq_one_iff _).mp hzN
      have hz2 : (u * (y ^ k)⁻¹) ^ 2 = 1 := hN2 _ hz
      have hcommk : Commute u ((y ^ k)⁻¹) := (show Commute u y from huy).zpow_right k |>.inv_right
      have hykpow : (y ^ k) ^ p = 1 := by
        rw [← zpow_natCast (y ^ k) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          ← hyord, pow_orderOf_eq_one, one_zpow]
      have hu_pow : u ^ p = 1 := by rw [← huord, pow_orderOf_eq_one]
      have hzpow : (u * (y ^ k)⁻¹) ^ p = 1 := by
        rw [hcommk.mul_pow, inv_pow, hu_pow, hykpow, inv_one, mul_one]
      have hz1 : u * (y ^ k)⁻¹ = 1 :=
        CFSG.GroupTheory.FrobeniusNormalComplement.orderOf_eq_one_of_dvd
          (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2))
          (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_of_pow_eq_one hzpow)
      have huyk : u = y ^ k := eq_of_mul_inv_eq_one hz1
      exact hunot (huyk ▸ Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)

@[expose] def K7bOmega8Model (r f p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (b c : K), Nat.card K = r ^ f →
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∃ A₀ : Subgroup (StatedOmega (StatedQuadMinus 4 K b c)),
      CFSG.Open.IsElemAbelian 3 A₀ ∧ Nat.card A₀ = 27 ∧ K7bOmega8Clause A₀ p

theorem k7b_pomega8m_of_model
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hY : IsLie811 Y .pomega8m r f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hM : K7bOmega8Model r f p)
    {A : Subgroup Y} (hA : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ y ∈ centralizer (A : Set Y), orderOf y = p ∧ ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      ∃ u ∈ centralizer (X : Set Y), orderOf u = p ∧ u * y = y * u ∧ u ∉ zpowers y := by
  have hcenter : center Y = ⊥ := center_eq_bot_of_isLie811_of_ne hY (by decide) (by simp)
  let e0 : Y ≃* Y ⧸ center Y :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  have hSCM : StatedClassicalModel (Y ⧸ center Y) .POmegaMinus 4 r f :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hY.2.2.2.2
  simp only [StatedClassicalModel] at hSCM
  obtain ⟨-, K, hK, hKfin, hKcard, b, c, hirr, ⟨e⟩⟩ := hSCM
  letI : Field K := hK
  letI : Finite K := hKfin
  let ι := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2
  let H : Subgroup (GL ι K) := StatedOmega (StatedQuadMinus 4 K b c)
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  haveI : N.Normal := inferInstance
  obtain ⟨A₀, hA₀ea, hA₀card, hA₀clause⟩ := hM K b c hKcard hirr
  let Q : (ι → K) → K := StatedQuadMinus 4 K b c
  have hQ : ∀ (d : K) (v : ι → K), Q (d • v) = d ^ 2 * Q v :=
    fun d v => (quadMinusForm 4 K b c hirr).Q_smul d v
  let v₀ : ι → K := Pi.single (Sum.inr (Sum.inr 0)) 1
  have hv₀ : Q v₀ ≠ 0 := by
    simp [Q, v₀, ι, StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]
  have hN2 : ∀ n ∈ N, n ^ 2 = 1 := by
    intro n hn
    have hs : ((n : H) : GL ι K) ∈ StatedScalars ι K := Subgroup.mem_subgroupOf.mp hn
    have hsq : ((n : H) : GL ι K) ^ 2 = 1 :=
      CFSG.HardMathSupport.Malle.E27Lie.sq_eq_one_of_mem_statedScalars hQ hv₀ (n : H).2 hs
    exact Subtype.ext (by simpa using hsq)
  have h3not : ¬ 3 ∣ Nat.card N :=
    CFSG.HardMathSupport.Malle.E27Lie.not_three_dvd_card_scalars_statedOmega hQ hv₀
  have hA₀proj : K7bOmega8Clause (A₀.map (QuotientGroup.mk' N)) p :=
    K7bOmega8Clause.map_mk hN2 hp hp2 (fun a ha => hA₀ea.2 a ha) hA₀clause
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : StatedProj H →* Y := e0.symm.toMonoidHom.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := e0.symm.injective.comp e.symm.injective
  let B : Subgroup Y := (A₀.map (QuotientGroup.mk' N)).map ψ
  have hBclause : K7bOmega8Clause B p :=
    K7bOmega8Clause.map_of_injective ψ hψ hA₀proj
  have hBea : CFSG.Open.IsElemAbelian 3 B := (hA₀ea.map (QuotientGroup.mk' N)).map ψ
  have hB27 : Nat.card B = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective hψ,
      CFSG.GroupTheory.CoprimeTransport.card_map_mk_eq_of_isPGroup (p := 3) h3not hA₀ea.isPGroup,
      hA₀card]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.UniqueElemSylow.exists_conj_eq
    (uniqueElemSylow_of_isLie811 hY) hBea hB27 hA (by rw [h27]; norm_num)
  have hAclause : K7bOmega8Clause A p := by
    simpa [hg] using K7bOmega8Clause.map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective hBclause
  exact hAclause

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
