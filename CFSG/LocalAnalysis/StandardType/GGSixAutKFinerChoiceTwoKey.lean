module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoComb
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCent

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Perfect

variable {G : Type*} [Group G]

theorem commutator_sup_le' {N Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (N : Set G)) :
    ⁅N ⊔ Y, N ⊔ Y⁆ ≤ N ⊔ ⁅Y, Y⁆ := by
  have hdec : ∀ g ∈ N ⊔ Y, ∃ n ∈ N, ∃ y ∈ Y, g = n * y := by
    intro g hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N Y hY] at hg
    obtain ⟨n, hn, y, hy, rfl⟩ := hg
    exact ⟨n, hn, y, hy, rfl⟩
  have hconj : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.1 (hY hy) n).1 hn
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  obtain ⟨n₁, hn₁, y₁, hy₁, rfl⟩ := hdec g₁ h₁
  obtain ⟨n₂, hn₂, y₂, hy₂, rfl⟩ := hdec g₂ h₂
  have hc : ⁅y₁, y₂⁆ ∈ ⁅Y, Y⁆ := Subgroup.commutator_mem_commutator hy₁ hy₂
  have hcY : ⁅y₁, y₂⁆ ∈ Y := Subgroup.commutator_le_self Y hc
  have hm₁ : n₁ * (y₁ * n₂ * y₁⁻¹) ∈ N := mul_mem hn₁ (hconj y₁ hy₁ n₂ hn₂)
  have hm₂ : n₂ * (y₂ * n₁ * y₂⁻¹) ∈ N := mul_mem hn₂ (hconj y₂ hy₂ n₁ hn₁)
  have e : ⁅n₁ * y₁, n₂ * y₂⁆ = n₁ * (y₁ * n₂ * y₁⁻¹) *
      (⁅y₁, y₂⁆ * (n₂ * (y₂ * n₁ * y₂⁻¹))⁻¹ * ⁅y₁, y₂⁆⁻¹) * ⁅y₁, y₂⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem hm₁ (hconj _ hcY _ (inv_mem hm₂))))
    (Subgroup.mem_sup_right hc)

theorem ggDer_le_self' (Y : Subgroup G) (k : ℕ) : LayerFacts.ggDer Y k ≤ Y := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [LayerFacts.ggDer_succ]
    exact (Subgroup.commutator_le_self _).trans ih

theorem le_of_perfect_of_le_sup {N Y Q : Subgroup G} (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hYs : Group.IsSolvable Y) (hQ : ⁅Q, Q⁆ = Q) (hQle : Q ≤ N ⊔ Y) : Q ≤ N := by
  have hder : ∀ k, LayerFacts.ggDer (N ⊔ Y) k ≤ N ⊔ LayerFacts.ggDer Y k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_succ]
      exact (Subgroup.commutator_mono ih ih).trans
        (commutator_sup_le' ((ggDer_le_self' Y k).trans hY))
  obtain ⟨k, hk⟩ := LayerCores.exists_ggDer_eq_bot hYs
  refine ClNonsplit.le_of_ggDer_le hQ hQle (k := k) ((hder k).trans ?_)
  rw [hk, sup_bot_eq]

end Perfect

section Supp

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {s : ℕ}

@[expose] def suppSub (K : Type) [Field K] [Algebra K L] (S : Finset (Fin s)) :
    Submodule K (Fin s → L) where
  carrier := {d | ∀ i, i ∉ S → d i = 0}
  add_mem' hd hd' i hi := by rw [Pi.add_apply, hd i hi, hd' i hi, add_zero]
  zero_mem' i _ := rfl
  smul_mem' c d hd i hi := by rw [Pi.smul_apply, hd i hi, smul_zero]

theorem mem_suppSub {S : Finset (Fin s)} {d : Fin s → L} :
    d ∈ suppSub (L := L) K S ↔ ∀ i, i ∉ S → d i = 0 := Iff.rfl

@[expose] noncomputable def suppSubEquiv (S : Finset (Fin s)) :
    suppSub (L := L) K S ≃ₗ[K] (S → L) where
  toFun d i := (d : Fin s → L) i
  invFun e := ⟨fun i => if h : i ∈ S then e ⟨i, h⟩ else 0, fun i hi => by simp [hi]⟩
  map_add' d d' := rfl
  map_smul' c d := rfl
  left_inv d := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ S
    · simp [h]
    · simp only [h, dite_false]
      exact (d.2 i h).symm
  right_inv e := by
    funext i
    simp

theorem finrank_suppSub [Module.Finite K L] (S : Finset (Fin s)) :
    finrank K (suppSub (L := L) K S) = S.card * finrank K L := by
  rw [LinearEquiv.finrank_eq (suppSubEquiv (K := K) (L := L) S), Module.finrank_pi_fintype]
  simp

end Supp

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L] [Algebra K L]
  {ζ : L} {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)

namespace SpFrame

@[expose] def zeroSet (c : Fin F.s → ZMod 3) : Finset (Fin F.s) :=
  Finset.univ.filter fun i => c i = 0

@[expose] def suppSet (c : Fin F.s → ZMod 3) : Finset (Fin F.s) :=
  Finset.univ.filter fun i => c i ≠ 0

omit [Finite K] [CharP K 2] in
theorem mem_zeroSet {c : Fin F.s → ZMod 3} {i : Fin F.s} : i ∈ F.zeroSet c ↔ c i = 0 := by
  simp [zeroSet]

omit [Finite K] [CharP K 2] in
theorem mem_suppSet {c : Fin F.s → ZMod 3} {i : Fin F.s} : i ∈ F.suppSet c ↔ c i ≠ 0 := by
  simp [suppSet]

omit [Finite K] [CharP K 2] in
theorem fix_eq_map (hζo : IsPrimitiveRoot ζ 3) (c : Fin F.s → ZMod 3) :
    primaryComponent (spEnd (F.tor c)) (X - 1) =
      (suppSub (L := L) K (F.zeroSet c)).map (F.Φ : (Fin F.s → L) →ₗ[K] _) := by
  ext v
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  rw [mem_primaryComponent, aeval_X_sub_one_apply, sub_eq_zero, F.tor_fix_iff hζo,
    Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_suppSub]
  simp only [mem_zeroSet]

omit [Finite K] in
theorem phi3_eq_map (hζo : IsPrimitiveRoot ζ 3) (c : Fin F.s → ZMod 3) :
    primaryComponent (spEnd (F.tor c)) (phi3 K) =
      (suppSub (L := L) K (F.suppSet c)).map (F.Φ : (Fin F.s → L) →ₗ[K] _) := by
  ext v
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  rw [mem_primaryComponent, aeval_phi3_apply, F.tor_phi3_iff hζo,
    Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_suppSub]
  simp only [mem_suppSet, not_not]

variable [Module.Finite K L]

omit [Finite K] [CharP K 2] in
theorem spFixedDim_tor (hζo : IsPrimitiveRoot ζ 3) (hL : finrank K L = 2)
    (c : Fin F.s → ZMod 3) : spFixedDim (F.tor c) = 2 * (F.zeroSet c).card := by
  rw [spFixedDim, F.fix_eq_map hζo, LinearEquiv.finrank_map_eq, finrank_suppSub, hL, mul_comm]

omit [Finite K] in
theorem finrank_phi3_tor (hζo : IsPrimitiveRoot ζ 3) (hL : finrank K L = 2)
    (c : Fin F.s → ZMod 3) :
    finrank K (primaryComponent (spEnd (F.tor c)) (phi3 K)) = 2 * (F.suppSet c).card := by
  rw [F.phi3_eq_map hζo, LinearEquiv.finrank_map_eq, finrank_suppSub, hL, mul_comm]

theorem mult_phi3_tor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3) (hL : finrank K L = 2)
    (c : Fin F.s → ZMod 3) :
    primaryMultiplicity (spEnd (F.tor c)) (phi3 K) = (F.suppSet c).card := by
  have : Fact (Irreducible (phi3 K)) := ⟨phi3_irreducible hK⟩
  have h1 := finrank_primaryComponent (x := spEnd (F.tor c)) (a := phi3 K)
  rw [F.finrank_phi3_tor hζo hL c, natDegree_phi3] at h1
  change finrank (AdjoinRoot (phi3 K)) (primaryComponent (spEnd (F.tor c)) (phi3 K)) = _
  omega

end SpFrame

end Frame

theorem reciprocal_phi3 {K : Type} [Field K] : reciprocalPolynomial (phi3 K) = phi3 K := by
  rw [reciprocalPolynomial, Polynomial.reverse, natDegree_phi3]
  have h0 : (phi3 K).coeff 0 = 1 := by simp [phi3]
  have hr : reflect 2 (phi3 K) = phi3 K := by
    have e : phi3 K = X ^ 2 + X ^ 1 + C 1 := by rw [phi3, pow_one, C_1]
    rw [e, reflect_add, reflect_add, reflect_monomial, reflect_monomial, reflect_C]
    simp only [revAt_le (show 2 ≤ 2 by norm_num), revAt_le (show 1 ≤ 2 by norm_num)]
    simp only [Nat.sub_self, pow_zero, Nat.reduceSub, pow_one, map_one, one_mul]
    ring
  rw [h0, inv_one, C_1, one_mul, hr]

section Key

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} [NeZero n] {L : Type} [Field L]
  [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)

namespace SpFrame

omit [Finite K] in
theorem blocks_tor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3) {c : Fin F.s → ZMod 3}
    (hc : c ≠ 0) : SpPrimaryBlocks 2 1 3 (F.tor c) (proj n K (F.tor c)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 := F.tor_pow_three hζo.pow_eq_one c
  have hx1 : F.tor c ≠ 1 := fun h => hc (F.tor_injective hζo (h.trans F.tor_zero.symm))
  have hxo : orderOf (F.tor c) = 3 := orderOf_eq_prime hx3 hx1
  have hinj : Function.Injective (proj n K) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact le_antisymm
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center.trans
        AutPSp.center_eq_bot.le) bot_le
  have hxop : orderOf (proj n K (F.tor c)) = 3 := by rw [orderOf_injective _ hinj, hxo]
  exact ((symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two le_rfl
    (by rw [hK, pow_one]) Nat.prime_three (by norm_num) (by norm_num)
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) _ hxop).2) _ rfl hxo

variable [Module.Finite K L]

theorem le_spFixedFactor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (hL : finrank K L = 2) {c : Fin F.s → ZMod 3} (hw : (F.suppSet c).card ≤ 3)
    {Q : Subgroup (StatedSp n K)} (hQ : ⁅Q, Q⁆ = Q)
    (hQc : Q ≤ Subgroup.centralizer {F.tor c}) : Q ≤ spFixedFactor (F.tor c) := by
  classical
  by_cases hc : c = 0
  ·
    subst hc
    intro g _
    refine mem_spSupported_of hK (F.tor_pow_three hζo.pow_eq_one 0) (by rw [F.tor_zero]; group)
      (fun h => absurd (Set.mem_singleton _) h) fun _ v hv => ?_
    rw [F.tor_zero, spEnd_one_apply, spEnd_one_apply] at hv
    have hv0 : v = 0 := by
      rw [add_self_eq_zero_of_charTwo (K := K), zero_add] at hv
      exact hv
    rw [hv0, map_zero]
  set x := F.tor c with hxdef
  have blocks := F.blocks_tor hK hζo hc
  have hx3 : x ^ 3 = 1 := F.tor_pow_three hζo.pow_eq_one c
  have hT3 : spEnd x ^ 3 = 1 := by rw [← spEnd_pow, hx3, spEnd_one]
  have hsupp : 0 < (F.suppSet c).card := by
    rw [Finset.card_pos]
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    exact hc (funext fun i => by
      by_contra hi
      have : i ∈ F.suppSet c := F.mem_suppSet.mpr hi
      rw [h0] at this
      exact Finset.notMem_empty i this)
  have hmem : phi3 K ∈ primaryFactors (spEnd x) := by
    by_contra hnm
    have hbot := primaryComponent_eq_bot_of_not_mem (phi3_irreducible hK) monic_phi3 hnm
    have hm := F.finrank_phi3_tor hζo hL c
    rw [hbot, finrank_bot] at hm
    omega
  set F₂ := spSupported x {phi3 K, reciprocalPolynomial (phi3 K)} with hF₂
  have hF₂' : F₂ = spSupported x {phi3 K} := by
    rw [hF₂, reciprocal_phi3, Set.pair_eq_singleton]
  have hle : Q ≤ spFixedFactor x ⊔ F₂ := by
    refine hQc.trans ?_
    rw [← blocks.directProduct.2.2]
    refine iSup_le fun O => ?_
    obtain ⟨O, k, hk, rfl⟩ := O
    rcases primaryFactor_cases hK hT3 hk with rfl | rfl
    · refine le_sup_of_le_left (le_of_eq ?_)
      change spSupported x {X - 1, reciprocalPolynomial (X - 1)} = spSupported x {X - 1}
      rw [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    · exact le_sup_right
  have hnorm : F₂ ≤ Subgroup.normalizer (spFixedFactor x : Set (StatedSp n K)) := by
    intro y hy
    have hyc := SevSpNs.spSupported_le_centralizer x _ hy
    have hyc' := Subgroup.inv_mem _ hyc
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg =>
      spFixedFactor_normalized x y hyc g hg, fun hg => ?_⟩
    have h1 := spFixedFactor_normalized x y⁻¹ hyc' _ hg
    simpa [mul_assoc] using h1
  have hsolv : Group.IsSolvable F₂ := by
    rw [hF₂']
    have hself : reciprocalPolynomial ((⟨phi3 K, hmem⟩ : primaryFactors (spEnd x)) : K[X]) =
        (⟨phi3 K, hmem⟩ : primaryFactors (spEnd x)) := reciprocal_phi3
    obtain ⟨d, hd2, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ :=
      (blocks.selfDual ⟨phi3 K, hmem⟩ phi3_ne_X_sub_one hself).exists_half
    have hfd : 1 * d = 1 := by
      have : (phi3 K).natDegree = 2 * d := hd2
      rw [natDegree_phi3] at this
      omega
    have hm : primaryMultiplicity (spEnd x) (phi3 K) = (F.suppSet c).card :=
      F.mult_phi3_tor hK hζo hL c
    by_cases hm2 : 2 ≤ primaryMultiplicity (spEnd x) (phi3 K)
    · exact SevSpNs.isSolvable_spSupported_selfDual hE hHf hHfl φ hfd hm2
        (show primaryMultiplicity (spEnd x) (phi3 K) ≤ 3 by omega)
    ·
      have : Fact (Irreducible ((⟨phi3 K, hmem⟩ : primaryFactors (spEnd x)) : K[X])) :=
        ⟨phi3_irreducible hK⟩
      have hcomm : ∀ g g' : spSupported x {phi3 K}, g * g' = g' * g := by
        intro g g'
        apply φ.injective
        rw [map_mul, map_mul]
        apply Subtype.ext
        apply Units.ext
        exact (KCUnitary.End_commute_of_finrank_le_one (Nat.lt_succ_iff.mp (not_le.mp hm2)) _ _).eq
      let _ : CommGroup (spSupported x {phi3 K}) := { mul_comm := hcomm }
      infer_instance
  exact le_of_perfect_of_le_sup hnorm hsolv hQ hle

end SpFrame

end Key

end ChoiceTwo

end CFSG.StandardType
