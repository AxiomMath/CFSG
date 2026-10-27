module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open scoped Pointwise

@[expose] def CartanAt {Y : Type} [Group Y] (U : Subgroup Y) (n : ℕ) (T : Type) [Group T] :
    Prop :=
  ∃ (D : Subgroup Y) (t : Y), D ≤ normalizer (U : Set Y) ∧ Nonempty (D ≃* T) ∧
    (∀ x ∈ normalizer (U : Set Y), x ^ (2 ^ n - 1) ∈ U ↔ x ∈ D ⊔ U) ∧
    (∃ k : ℕ, orderOf t = 2 ^ k) ∧ ∀ a ∈ D, t * a * t⁻¹ = a⁻¹

theorem CartanAt.map {Y Y' : Type} [Group Y] [Group Y'] {U : Subgroup Y} {n : ℕ} {T : Type}
    [Group T] (h : CartanAt U n T) (e : Y ≃* Y') : CartanAt (U.map e.toMonoidHom) n T := by
  obtain ⟨D, t, hDN, ⟨eD⟩, hiff, ⟨k, hk⟩, hinv⟩ := h
  have hN : normalizer ((U.map e.toMonoidHom : Subgroup Y') : Set Y') =
      (normalizer (U : Set Y)).map e.toMonoidHom := (map_equiv_normalizer_eq U e).symm
  refine ⟨D.map e.toMonoidHom, e t, ?_,
    ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eD⟩, ?_,
    ⟨k, by rw [MulEquiv.orderOf_eq, hk]⟩, ?_⟩
  · rw [hN]
    exact map_mono hDN
  · intro x hx
    rw [hN, mem_map_equiv] at hx
    have h1 := hiff (e.symm x) hx
    rw [mem_map_equiv, ← Subgroup.map_sup, mem_map_equiv, map_pow]
    exact h1
  · intro a ha
    rw [mem_map_equiv] at ha
    have h1 := hinv (e.symm a) ha
    have h2 := congrArg e h1
    rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply] at h2
    exact h2

theorem isSylowOf_map_equiv {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    {U : Subgroup Y} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (e : Y ≃* Y') :
    CFSG.ABGLocalTools.IsSylowOf 2 (U.map e.toMonoidHom) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp, hi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hU
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hp.map _, ?_⟩
  rw [relIndex_top_right] at hi ⊢
  rwa [show (U.map e.toMonoidHom) = U.map (e : Y →* Y') from rfl, index_map_equiv]

theorem CartanAt.of_isSylowOf {Y : Type} [Group Y] [Finite Y] {U₀ U : Subgroup Y} {n : ℕ}
    {T : Type} [Group T] (h : CartanAt U₀ n T) (hU₀ : CFSG.ABGLocalTools.IsSylowOf 2 U₀ ⊤)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) : CartanAt U n T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp₀, hi₀⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hU₀
  obtain ⟨-, hp, hi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hU
  rw [relIndex_top_right] at hi₀ hi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (hp₀.toSylow hi₀) (hp.toSylow hi)
  have hUg : U = U₀.map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hg
    simp only [Sylow.pointwise_smul_def, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    rfl
  rw [hUg]
  exact h.map (MulAut.conj g)

theorem mem_normalizer_prod_iff {A B : Type} [Group A] [Group B] {U : Subgroup A}
    {V : Subgroup B} {a : A} {b : B} :
    (a, b) ∈ normalizer ((U.prod V : Subgroup (A × B)) : Set (A × B)) ↔
      a ∈ normalizer (U : Set A) ∧ b ∈ normalizer (V : Set B) := by
  simp only [mem_normalizer_iff]
  constructor
  · intro h
    refine ⟨fun u => ?_, fun v => ?_⟩
    · have := h (u, 1)
      simpa [mem_prod] using this
    · have := h (1, v)
      simpa [mem_prod] using this
  · rintro ⟨ha, hb⟩ ⟨u, v⟩
    simp only [mem_prod, Prod.mk_mul_mk, Prod.inv_mk]
    exact and_congr (ha u) (hb v)

theorem prod_sup_prod_of_le_normalizer {A B : Type} [Group A] [Group B] {D U : Subgroup A}
    {E V : Subgroup B} (hD : D ≤ normalizer (U : Set A)) (hE : E ≤ normalizer (V : Set B)) :
    D.prod E ⊔ U.prod V = (D ⊔ U).prod (E ⊔ V) := by
  apply le_antisymm
  · exact sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha' : a ∈ ((D : Set A) * (U : Set A)) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hD]
      exact ha
    have hb' : b ∈ ((E : Set B) * (V : Set B)) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hE]
      exact hb
    obtain ⟨d, hd, u, hu, rfl⟩ := ha'
    obtain ⟨e, he, v, hv, rfl⟩ := hb'
    have : ((d * u, e * v) : A × B) = (d, e) * (u, v) := rfl
    rw [this]
    exact mul_mem_sup ⟨hd, he⟩ ⟨hu, hv⟩

theorem CartanAt.prod {A B : Type} [Group A] [Group B] {U : Subgroup A} {V : Subgroup B} {n : ℕ}
    (hU : CartanAt U n (Multiplicative (ZMod (2 ^ n - 1))))
    (hV : CartanAt V n (Multiplicative (ZMod (2 ^ n - 1)))) :
    CartanAt (U.prod V) n (Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1))) := by
  obtain ⟨D, t, hDN, ⟨eD⟩, hiffD, ⟨k, hk⟩, hinvD⟩ := hU
  obtain ⟨E, s, hEN, ⟨eE⟩, hiffE, ⟨l, hl⟩, hinvE⟩ := hV
  refine ⟨D.prod E, (t, s), ?_, ⟨?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact mem_normalizer_prod_iff.mpr ⟨hDN ha, hEN hb⟩
  · exact (D.prodEquiv E).trans ((eD.prodCongr eE).trans
      (MulEquiv.prodMultiplicative (G := ZMod (2 ^ n - 1)) (H := ZMod (2 ^ n - 1))).symm)
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb⟩ := mem_normalizer_prod_iff.mp hx
    rw [prod_sup_prod_of_le_normalizer hDN hEN, Prod.pow_mk, mem_prod, mem_prod]
    exact and_congr (hiffD a ha) (hiffE b hb)
  · have hdvd : orderOf (t, s) ∣ 2 ^ (k + l) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [Prod.pow_mk, pow_add, pow_mul, ← hk, pow_orderOf_eq_one, one_pow, mul_comm, pow_mul,
        ← hl, pow_orderOf_eq_one, one_pow, Prod.mk_one_one]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [Prod.mk_mul_mk, Prod.inv_mk, hinvD a ha, hinvE b hb]

theorem isSylowOf_prod {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {U : Subgroup A}
    {V : Subgroup B} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤)
    (hV : CFSG.ABGLocalTools.IsSylowOf 2 V ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (U.prod V) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hpU, hiU⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hU
  obtain ⟨-, hpV, hiV⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hV
  rw [relIndex_top_right] at hiU hiV
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hpU
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hpV
    refine IsPGroup.of_card (n := a + b) ?_
    rw [Nat.card_congr (U.prodEquiv V).toEquiv, Nat.card_prod, ha, hb, pow_add]
  · rw [relIndex_top_right, index_prod]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    exacts [hiU h, hiV h]

theorem k_19_glue4_torus_of_families
    (hSp4 : ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 3 ≤ n → IsSp4 X n →
      ∃ U : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
        CartanAt U n (Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1))))
    (hL2 : ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 3 ≤ n → IsL2 Y n →
      ∃ U : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
        CartanAt U n (Multiplicative (ZMod (2 ^ n - 1))))
    (hSz : ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 3 ≤ n → IsSz Y n →
      ∃ U : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
        CartanAt U n (Multiplicative (ZMod (2 ^ n - 1))))
    (hU3 : ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 3 ≤ n → IsU3 Y n →
      ∃ U : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
        CartanAt U n (Multiplicative (ZMod (2 ^ n - 1)))) :
    K_19_glue4_torus := by
  intro X _ _ n hn hX U hU
  suffices hex : ∃ U₀ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 U₀ ⊤ ∧
      CartanAt U₀ n (Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1))) by
    obtain ⟨U₀, hU₀, hC⟩ := hex
    exact hC.of_isSylowOf hU₀ hU
  have hprod : ∀ (A B : Type) [Group A] [Group B], Nonempty (X ≃* A × B) →
      (∀ [Finite A], ∃ UA : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 UA ⊤ ∧
        CartanAt UA n (Multiplicative (ZMod (2 ^ n - 1)))) →
      (∀ [Finite B], ∃ UB : Subgroup B, CFSG.ABGLocalTools.IsSylowOf 2 UB ⊤ ∧
        CartanAt UB n (Multiplicative (ZMod (2 ^ n - 1)))) →
      ∃ U₀ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 U₀ ⊤ ∧
        CartanAt U₀ n (Multiplicative (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1))) := by
    intro A B _ _ ⟨e⟩ hA hB
    haveI : Finite (A × B) := Finite.of_equiv X e.toEquiv
    haveI : Finite A := Finite.prod_left B
    haveI : Finite B := Finite.prod_right A
    obtain ⟨UA, hUA, hCA⟩ := hA
    obtain ⟨UB, hUB, hCB⟩ := hB
    refine ⟨(UA.prod UB).map e.symm.toMonoidHom, isSylowOf_map_equiv (isSylowOf_prod hUA hUB) _,
      (hCA.prod hCB).map e.symm⟩
  rcases hX with hX | hX | hX | hX
  · exact hSp4 X n hn hX
  · obtain ⟨A, B, _, _, he, hA, hB⟩ := hX
    exact hprod A B he (hL2 A n hn hA) (hL2 B n hn hB)
  · obtain ⟨A, B, _, _, he, hA, hB⟩ := hX
    exact hprod A B he (hSz A n hn hA) (hSz B n hn hB)
  · obtain ⟨A, B, _, _, he, hA, hB⟩ := hX
    exact hprod A B he (hL2 A n hn hA) (hU3 B n hn hB)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
