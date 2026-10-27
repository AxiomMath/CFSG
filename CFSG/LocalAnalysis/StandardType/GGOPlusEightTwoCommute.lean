module

public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoCount
public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoTri

public section

namespace CFSG.StandardType

namespace OPlusEight

namespace Cnt

open scoped Classical

section Top

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V] [Fintype V]

theorem qsum_bot (Q : QuadraticForm K V) : qsum Q ⊥ = 1 := by
  unfold qsum
  rw [Finset.sum_eq_single (0 : (⊥ : Submodule K V))]
  · simp [chi_zero]
  · intro b _ hb
    exact absurd (Subtype.ext ((Submodule.mem_bot K).mp b.2)) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

end Top

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K] [CharP K 2] [Fintype K]

theorem qsum_top_plus (hcard : Nat.card K = 2) : qsum (coordinateQuadPlus 4 K) ⊤ = 16 := by
  have hK := eq_zero_or_one_of_card_two hcard
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  unfold qsum
  have h1 : ∑ v : (⊤ : Submodule K (Fin (2 * 4) → K)),
      chi (coordinateQuadPlus 4 K (v : Fin (2 * 4) → K)) =
        ∑ v : Fin (2 * 4) → K, chi (coordinateQuadPlus 4 K v) :=
    Fintype.sum_equiv Submodule.topEquiv.toEquiv _ _ (fun v => rfl)
  rw [h1]
  have h2 : ∑ v : Fin (2 * 4) → K, chi (coordinateQuadPlus 4 K v) =
      ∑ w : (Fin 4 ⊕ Fin 4 → K), chi (∑ i, w (Sum.inl i) * w (Sum.inr i)) := by
    refine (Fintype.sum_equiv ((plusIndexEquiv 4).arrowCongr (Equiv.refl K)) _ _ (fun w => ?_)).symm
    rw [coordinateQuadPlus_apply]
    simp [Equiv.arrowCongr_apply]
  rw [h2]
  have h3 : ∑ w : (Fin 4 ⊕ Fin 4 → K), chi (∑ i, w (Sum.inl i) * w (Sum.inr i)) =
      ∑ p : (Fin 4 → K) × (Fin 4 → K), chi (∑ i, p.1 i * p.2 i) :=
    Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow (Fin 4) (Fin 4) K) _ _ (fun w => rfl)
  rw [h3, Fintype.sum_prod_type]
  have h4 : ∀ a : Fin 4 → K, ∑ b : Fin 4 → K, chi (∑ i, a i * b i) = if a = 0 then 16 else 0 := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp [chi_zero, Fintype.card_fun, hc]
    · rw [if_neg ha]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
      refine sum_chi_eq_zero hK _ (fun b b' => ?_) ⟨Pi.single i 1, ?_⟩
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      · simpa [Pi.single_apply] using hi
  simp only [h4]
  simp

end Plus

section Assembly

open CFSG.RankThree.PartOne.KCOrthogonal Module

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype V]

theorem reg_fixed {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    ∀ u ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x,
      (∀ w ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x, QuadraticMap.polar Q u w = 0) → u = 0 := by
  intro u hu hperp
  have hu' : u ∈ fixedSpace x := by rw [OrthRestOdd.fixedSpace_eq_lit]; exact hu
  have h := hx.polarBilin_fixed_nondegenerate.1 ⟨u, hu'⟩ (fun w => ?_)
  · exact congrArg Subtype.val h
  · rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype]
    exact hperp (w : V) (by rw [← OrthRestOdd.fixedSpace_eq_lit]; exact w.2)

theorem card_sub [Finite K] (hcard : Nat.card K = 2) (S : Submodule K V) :
    Fintype.card S = 2 ^ finrank K S := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [Module.card_eq_pow_finrank (K := K) (V := S), ← Nat.card_eq_fintype_card, hcard]

theorem pow_apply_of_fixed {g : V ≃ₗ[K] V} {v : V} (h : g v = v) (n : ℕ) : (g ^ n) v = v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, h, ih]

theorem fix_of_coprime {g : V ≃ₗ[K] V} {v : V} {a b : ℕ} (hgb : g ^ b = 1)
    (hab : Nat.Coprime a b) (hb : 1 < b) (h : (g ^ a) v = v) : g v = v := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hab hb
  have h1 : g ^ (a * m) = g := by rw [pow_eq_pow_mod _ hgb, hm, pow_one]
  have h2 : (g ^ (a * m)) v = v := by
    rw [pow_mul]
    exact pow_apply_of_fixed h m
  rwa [h1] at h2

theorem fixed_mul_eq {x y : V ≃ₗ[K] V} (hxy : x * y = y * x) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hx3 : x ^ 3 = 1) (hyq : y ^ q = 1) :
    CFSG.RankThree.PartOne.LIT.fixedSpace x ⊓ CFSG.RankThree.PartOne.LIT.fixedSpace y =
      CFSG.RankThree.PartOne.LIT.fixedSpace (x * y) := by
  have hcop : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).mpr (by omega)
  ext v
  simp only [Submodule.mem_inf, CFSG.RankThree.PartOne.LIT.mem_fixedSpace]
  constructor
  · rintro ⟨h1, h2⟩
    rw [LinearEquiv.mul_apply, h2, h1]
  · intro h
    have hxyc : Commute x y := hxy
    have hpow := pow_apply_of_fixed h
    have h3 : (x * y) ^ 3 = y ^ 3 := by rw [hxyc.mul_pow, hx3, one_mul]
    have hq' : (x * y) ^ q = x ^ q := by rw [hxyc.mul_pow, hyq, mul_one]
    refine ⟨fix_of_coprime hx3 hcop.symm (by norm_num) (by rw [← hq']; exact hpow q), ?_⟩
    exact fix_of_coprime hyq hcop hq.one_lt (by rw [← h3]; exact hpow 3)


theorem no_commuting_prime [Finite K] (hcard : Nat.card K = 2) (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    (hV : qsum Q ⊤ = 16) {x y : V ≃ₗ[K] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxy : x * y = y * x) (hx3 : x ^ 3 = 1)
    {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hyq : y ^ q = 1) (hy1 : y ≠ 1)
    (hd : finrank K (CFSG.RankThree.PartOne.LIT.fixedSpace x) = 2 ∨
      finrank K (CFSG.RankThree.PartOne.LIT.fixedSpace x) = 4) : False := by
  have hK := eq_zero_or_one_of_card_two hcard
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have h3K : ((3 : ℕ) : K) ≠ 0 := OrthRestOdd.natCast_ne_zero_of_odd Nat.prime_three (by norm_num)
  have hqK : ((q : ℕ) : K) ≠ 0 := OrthRestOdd.natCast_ne_zero_of_odd hq hq2
  have hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0 := fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]; exact hv w
  have hx : OddOrderIsometry Q 3 x := ⟨hxO, hx3, h3K, hreg⟩
  have hy : OddOrderIsometry Q q y := ⟨hyO, hyq, hqK, hreg⟩
  have hxyc : Commute x y := hxy
  have hxyp : (x * y) ^ (3 * q) = 1 := by
    have h1 : x ^ (3 * q) = 1 := by rw [pow_mul, hx3, one_pow]
    have h2 : y ^ (3 * q) = 1 := by rw [mul_comm, pow_mul, hyq, one_pow]
    rw [hxyc.mul_pow, h1, h2, one_mul]
  have hxy' : OddOrderIsometry Q (3 * q) (x * y) :=
    ⟨Subgroup.mul_mem _ hxO hyO, hxyp, by rw [Nat.cast_mul]; exact mul_ne_zero h3K hqK, hreg⟩
  have hZeq := fixed_mul_eq hxy hq hq3 hx3 hyq
  have hxQ : ∀ v, Q (x v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hxO
  have hyQ : ∀ v, Q (y v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hyO
  have hcomm : ∀ v, x (y v) = y (x v) := fun v => by
    rw [← LinearEquiv.mul_apply, hxy, LinearEquiv.mul_apply]
  set U := CFSG.RankThree.PartOne.LIT.fixedSpace x with hU
  set F := CFSG.RankThree.PartOne.LIT.fixedSpace y with hF
  have hUinv : ∀ v ∈ U, y v ∈ U := fun v hv => by
    rw [hU, CFSG.RankThree.PartOne.LIT.mem_fixedSpace] at hv ⊢
    rw [hcomm, hv]
  have hFinv : ∀ v ∈ F, x v ∈ F := fun v hv => by
    rw [hF, CFSG.RankThree.PartOne.LIT.mem_fixedSpace] at hv ⊢
    rw [← hcomm, hv]
  obtain ⟨jU, hjU, hqU⟩ := qsum_eq hcard Q U (reg_fixed hx)
  obtain ⟨jF, hjF, hqF⟩ := qsum_eq hcard Q F (reg_fixed hy)
  obtain ⟨jZ, hjZ, hqZ⟩ := qsum_eq hcard Q (U ⊓ F) (by rw [hZeq]; exact reg_fixed hxy')
  have hFle : finrank K F ≤ 8 := hdim ▸ Submodule.finrank_le F
  have hFne : finrank K F ≠ 8 := by
    intro h8
    apply hy1
    have htop : F = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h8, hdim])
    ext v
    have hv : v ∈ F := htop ▸ Submodule.mem_top
    exact CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp hv
  have hZU : finrank K ↥(U ⊓ F) ≤ finrank K U := Submodule.finrank_mono inf_le_left
  have hZF : finrank K ↥(U ⊓ F) ≤ finrank K F := Submodule.finrank_mono inf_le_right
  have hsum : finrank K U + finrank K F ≤ 8 + finrank K ↥(U ⊓ F) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U F
    have h2 : finrank K ↥(U ⊔ F) ≤ 8 := hdim ▸ Submodule.finrank_le _
    omega
  have hbot : ∀ S : Submodule K V, finrank K S = 0 → qsum Q S = 1 := fun S hS => by
    rw [Submodule.finrank_eq_zero.mp hS]
    exact qsum_bot Q
  have h2 : (16 : ℤ) ≡ qsum Q U [ZMOD 3] := by
    have h := qsum_modEq hK (p := 3) Q x hxQ hx3 ⊤ (fun v _ => Submodule.mem_top)
    rw [hV, top_inf_eq] at h
    exact_mod_cast h
  have h3 : ((2 : ℤ) ^ 8) ≡ 2 ^ finrank K F [ZMOD q] := by
    have h := card_modEq (p := q) y hyq ⊤ (fun v _ => Submodule.mem_top)
    rw [top_inf_eq, card_sub hcard, card_sub hcard, finrank_top, hdim] at h
    exact_mod_cast Int.natCast_modEq_iff.mpr h
  have h4 : (16 : ℤ) ≡ qsum Q F [ZMOD q] := by
    have h := qsum_modEq hK (p := q) Q y hyQ hyq ⊤ (fun v _ => Submodule.mem_top)
    rw [hV, top_inf_eq] at h
    exact_mod_cast h
  have h5 : ((2 : ℤ) ^ finrank K U) ≡ 2 ^ finrank K ↥(U ⊓ F) [ZMOD q] := by
    have h := card_modEq (p := q) y hyq U hUinv
    rw [card_sub hcard, card_sub hcard] at h
    exact_mod_cast Int.natCast_modEq_iff.mpr h
  have h6 : qsum Q U ≡ qsum Q (U ⊓ F) [ZMOD q] := by
    have h := qsum_modEq hK (p := q) Q y hyQ hyq U hUinv
    exact_mod_cast h
  have h7 : ((2 : ℤ) ^ finrank K F) ≡ 2 ^ finrank K ↥(U ⊓ F) [ZMOD 3] := by
    have h := card_modEq (p := 3) x hx3 F hFinv
    rw [← inf_comm, card_sub hcard, card_sub hcard] at h
    exact_mod_cast Int.natCast_modEq_iff.mpr h
  have h8 : qsum Q F ≡ qsum Q (U ⊓ F) [ZMOD 3] := by
    have h := qsum_modEq hK (p := 3) Q x hxQ hx3 F hFinv
    rw [← inf_comm] at h
    exact_mod_cast h
  have hdU : finrank K U / 2 = jU := by omega
  have hdF : finrank K F / 2 = jF := by omega
  have hdZ : finrank K ↥(U ⊓ F) / 2 = jZ := by omega
  refine arith_contra q hq hq3 (finrank K U) (finrank K F) (finrank K ↥(U ⊓ F)) hd (by omega)
    (by omega) hZU hZF hsum (qsum Q U) (qsum Q F) (qsum Q (U ⊓ F)) ?_ ?_ ?_ ?_ ?_ h2 h3 h4 h5 h6 h7
    h8
  · rw [hdU]; exact hqU
  · rw [hdF]; exact hqF
  · rw [hdZ]; exact hqZ
  · intro h0; exact hbot F h0
  · intro h0; exact hbot _ h0

end Assembly

end Cnt

open CFSG.Assembly TableBSymp CFSG.StandardType.Triality CFSG.StandardType.D4Rank
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem midClassCommuteInput_holds : MidClassCommuteInput := by
  intro K _ _ hK t ht3 hd g hg q hq hq3 hgq
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hK'
  obtain ⟨hnd, -⟩ := regular_coordinateQuadPlus (K := K) (n := 4) (by norm_num)
  set Q := coordinateQuadPlus 4 K with hQ
  let φ : Om8 K ≃* CFSG.RankThree.Classical2.orthDerived Q :=
    CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q
  have htp : (φ t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
  have hxp : ((φ t : CFSG.RankThree.Classical2.orthDerived Q) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, htp]
    rfl
  have hgp : (φ g) ^ q = 1 := by rw [← map_pow, ← hgq, pow_orderOf_eq_one, map_one]
  have hyq : ((φ g : CFSG.RankThree.Classical2.orthDerived Q) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ^ q = 1 := by
    rw [← Subgroup.coe_pow, hgp]
    rfl
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hgq
    omega
  have hy1 : ((φ g : CFSG.RankThree.Classical2.orthDerived Q) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ≠ 1 := by
    intro h
    apply hg1
    apply φ.injective
    rw [map_one]
    exact Subtype.ext h
  have hxy : ((φ t : CFSG.RankThree.Classical2.orthDerived Q) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) *
        ((φ g : CFSG.RankThree.Classical2.orthDerived Q) :
          (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) =
      ((φ g : CFSG.RankThree.Classical2.orthDerived Q) :
          (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) *
        ((φ t : CFSG.RankThree.Classical2.orthDerived Q) :
          (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) := by
    have h := congrArg (fun a => ((φ a : CFSG.RankThree.Classical2.orthDerived Q) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) hg
    simp only [map_mul, Subgroup.coe_mul] at h
    exact h.symm
  exact Cnt.no_commuting_prime hK Q hnd (by rw [Module.finrank_fin_fun]) (Cnt.qsum_top_plus hK)
    (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (φ t).2)
    (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (φ g).2) hxy hxp hq hq3
    hyq hy1 (by rw [← omFixDim_eq_finrank_fixedSpace]; exact hd)

end OPlusEight

end CFSG.StandardType

end
