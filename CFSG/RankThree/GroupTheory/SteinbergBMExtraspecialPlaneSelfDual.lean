module

public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.CharP.Two

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup Module Polynomial CFSG CFSG.LinearAlgebra
open scoped commutatorElement

theorem dvd_two_pow_half_add_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hord : orderOf (2 : ZMod p) = p - 1) : p ∣ 2 ^ ((p - 1) / 2) + 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have h3 : 3 ≤ p := by have := hp.out.two_le; omega
  have ht2 : (2 : ZMod p) ^ ((p - 1) / 2) * (2 : ZMod p) ^ ((p - 1) / 2) = 1 := by
    rw [← pow_add, show (p - 1) / 2 + (p - 1) / 2 = p - 1 by omega, ← hord, pow_orderOf_eq_one]
  rcases mul_self_eq_one_iff.mp ht2 with h | h
  · exfalso
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, h,
      neg_add_cancel]

theorem exists_nondegenerate_bilin_frobenius_invariant {K : Type*} [Field K]
    [Algebra (ZMod 2) K] [Finite K] (s : ℕ) : ∃ B : K →ₗ[ZMod 2] K →ₗ[ZMod 2] ZMod 2,
      (∀ a, (∀ b, B a b = 0) → a = 0) ∧ (∀ b, (∀ a, B a b = 0) → b = 0) ∧
      ∀ κ : K, κ ^ (2 ^ s + 1) = 1 → ∀ a b, B (κ * a) (κ * b) = B a b := by
  have h2 : (2 : K) = 0 := by
    have h : (2 : ZMod 2) = 0 := by decide
    rw [← map_ofNat (algebraMap (ZMod 2) K) 2, h, map_zero]
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  set σ := iterateFrobenius K 2 s with hσ
  have hσapp : ∀ a, σ a = a ^ 2 ^ s := fun _ => rfl
  have hσinj : Function.Injective σ := σ.injective
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  have hσsmul : ∀ (r : ZMod 2) (a : K), σ (r • a) = r • σ a := by
    intro r a
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact RingHom.congr_fun
      (Subsingleton.elim (σ.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K)) r
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual (ZMod 2) K, ℓ 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) (1 : K)).mp h)
  refine ⟨LinearMap.mk₂ (ZMod 2) (fun a b => ℓ (a * σ b))
    (fun a a' b => by rw [add_mul, map_add]) (fun r a b => by rw [smul_mul_assoc, map_smul])
    (fun a b b' => by rw [map_add, mul_add, map_add])
    (fun r a b => by rw [hσsmul, mul_smul_comm, map_smul]), ?_, ?_, ?_⟩
  · intro a ha
    by_contra ha0
    obtain ⟨b, hb⟩ := hσsurj a⁻¹
    apply hℓ
    have h := ha b
    rw [LinearMap.mk₂_apply, hb, mul_inv_cancel₀ ha0] at h
    exact h
  · intro b hb
    by_contra hb0
    have hσb : σ b ≠ 0 := fun h => hb0 (hσinj (h.trans (map_zero σ).symm))
    apply hℓ
    have h := hb (σ b)⁻¹
    rw [LinearMap.mk₂_apply, inv_mul_cancel₀ hσb] at h
    exact h
  · intro κ hκ a b
    simp only [LinearMap.mk₂_apply]
    congr 1
    rw [map_mul, hσapp κ]
    calc κ * a * (κ ^ 2 ^ s * σ b) = κ ^ (2 ^ s + 1) * (a * σ b) := by ring
      _ = a * σ b := by rw [hκ, one_mul]

theorem extraspecial_cyclotomic_minimal_module_abelian_plane_self_dual {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hord : orderOf (2 : ZMod p) = p - 1) {Q : Type*}
    [Group Q] (hQ : IsExtraspecialPGroup p Q) (hcard : Nat.card Q = p ^ 3)
    (hexp : Monoid.exponent Q = p) {z : Q} (hz : zpowers z = center Q) {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) {r : ℕ} (hV : finrank (ZMod 2) V = p * (p - 1) + r)
    (hU : finrank (ZMod 2) (centralFixed ρ z) = r)
    (E : Subgroup Q) (hE : Nat.card E = p ^ 2) :
    ∃ (M : Fin p → Submodule (ZMod 2) V) (hM : ∀ i, ∀ e ∈ E, ∀ m ∈ M i, ρ e m ∈ M i),
      iSupIndep M ∧ ⨆ i, M i = centralImage ρ z ∧ (∀ i, finrank (ZMod 2) (M i) = p - 1) ∧
      (∀ i, ∀ S : Submodule (ZMod 2) V, S ≤ M i → (∀ e ∈ E, ∀ s ∈ S, ρ e s ∈ S) →
        S = ⊥ ∨ S = M i) ∧
      (∀ i j, i ≠ j → ∀ φ : M i ≃ₗ[ZMod 2] M j, ¬ ∀ (e : Q) (he : e ∈ E) (m : M i),
        φ ⟨ρ e m, hM i e he m m.2⟩ = ⟨ρ e (φ m), hM j e he _ (φ m).2⟩) ∧
      ∀ i, ∃ B : M i →ₗ[ZMod 2] M i →ₗ[ZMod 2] ZMod 2,
        (∀ a, (∀ b, B a b = 0) → a = 0) ∧ (∀ b, (∀ a, B a b = 0) → b = 0) ∧
        ∀ (e : Q) (he : e ∈ E) (a b : M i),
          B ⟨ρ e a, hM i e he a a.2⟩ ⟨ρ e b, hM i e he b b.2⟩ = B a b := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.out.ne_zero)
  have hzZ : z ∈ center Q := hz ▸ mem_zpowers z
  have hzc : ∀ g : Q, Commute g z := fun g => mem_center_iff.mp hzZ g
  have hexp' : ∀ g : Q, g ^ p = 1 := fun g => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one g
  have hTp : ρ z ^ p = 1 := by rw [← map_pow, hexp', map_one]
  have hΦ := irreducible_cyclotomic_two hp2 hord
  have hUW := isCompl_centralFixed_centralImage hp2 hTp
  have hWdim : finrank (ZMod 2) (centralImage ρ z) = p * (p - 1) := by
    have := Submodule.finrank_add_eq_of_isCompl hUW
    omega
  have : Nontrivial (centralImage ρ z) := Module.nontrivial_of_finrank_pos (R := ZMod 2)
    (by rw [hWdim]; exact Nat.mul_pos hp.out.pos hp1)
  have hKzero := aeval_centralImageOp_cyclotomic hp2 hTp
  have hK : IsField (centralImageAlgebra ρ z) :=
    isField_adjoin_singleton_of_aeval_eq_zero hΦ _ hKzero
  have hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = p - 1 := by
    rw [centralImageAlgebra, finrank_adjoin_singleton_of_aeval_eq_zero hΦ
      (cyclotomic.monic p (ZMod 2)) _ hKzero, natDegree_cyclotomic_two]
  have hzE : z ∈ E := by
    have hidx : E.index = p := by
      have h := card_mul_index E
      rw [hE, hcard, show p ^ 3 = p ^ 2 * p by ring] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos 2) h
    have hle := frattini_le_coatom (isCoatom_of_index_prime (H := E) (by rw [hidx]; exact hp.out))
    rw [hQ.2.2.1, ← hz] at hle
    exact hle (mem_zpowers z)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hE).is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x, hxE, hxZ⟩ : ∃ x ∈ E, x ∉ center Q := by
    by_contra h
    push Not at h
    have hle := card_le_of_le (show E ≤ center Q from fun x hx => h x hx)
    rw [hE, hQ.2.2.2] at hle
    have : p < p ^ 2 := by nlinarith [hp.out.two_le]
    omega
  obtain ⟨y, hyx⟩ : ∃ y : Q, y⁻¹ * x * y = x * z := by
    obtain ⟨g, hg⟩ : ∃ g : Q, g * x ≠ x * g := by
      by_contra h
      push Not at h
      exact hxZ (mem_center_iff.mpr h)
    set c := x⁻¹ * (g⁻¹ * x * g) with hc
    have hcZ : c ∈ center Q := by
      rw [← hQ.2.1]
      have e : c = ⁅x⁻¹, g⁻¹⁆ := by
        rw [hc, commutatorElement_def, inv_inv, inv_inv]
        group
      rw [e, commutator_eq_closure]
      exact subset_closure (commutator_mem_commutatorSet _ _)
    have hc1 : c ≠ 1 := by
      intro h1
      apply hg
      have h' : x = g⁻¹ * x * g := inv_mul_eq_one.mp (by rw [← hc]; exact h1)
      calc g * x = g * (g⁻¹ * x * g) := by rw [← h']
        _ = x * g := by group
    have hcc : ∀ h : Q, h * c = c * h := fun h => mem_center_iff.mp hcZ h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, z ^ m = c := by
      have hcz : c ∈ zpowers z := hz ▸ hcZ
      exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hcz)
    have hpm : ¬ p ∣ m := by
      rintro ⟨t, rfl⟩
      apply hc1
      rw [← hm, pow_mul, hexp', one_pow]
    obtain ⟨k, hk⟩ := exists_pow_pow_eq_self (hexp' z) hpm
    have hgxg : g⁻¹ * x * g = x * c := by rw [hc]; group
    have hiter : ∀ n : ℕ, (g ^ n)⁻¹ * x * g ^ n = x * c ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hcn : g⁻¹ * c ^ n * g = c ^ n := by
          rw [mul_assoc, ← ((Commute.pow_right (hcc g) n)).eq, ← mul_assoc, inv_mul_cancel,
            one_mul]
        calc (g ^ (n + 1))⁻¹ * x * g ^ (n + 1) = g⁻¹ * ((g ^ n)⁻¹ * x * g ^ n) * g := by
              rw [pow_succ]; group
          _ = g⁻¹ * (x * c ^ n) * g := by rw [ih]
          _ = (g⁻¹ * x * g) * (g⁻¹ * c ^ n * g) := by group
          _ = x * c * c ^ n := by rw [hgxg, hcn]
          _ = x * c ^ (n + 1) := by rw [pow_succ', mul_assoc]
    refine ⟨g ^ k, ?_⟩
    rw [hiter, ← hm, hk]
  obtain ⟨M, hMdef⟩ : ∃ M : Fin p → Submodule (ZMod 2) V, ∀ i, M i = cosetFixed ρ z x i :=
    ⟨fun i => cosetFixed ρ z x i, fun _ => rfl⟩
  have hWle : ∀ i, M i ≤ centralImage ρ z := fun i w hw => by
    rw [hMdef] at hw
    exact (mem_cosetFixed.mp hw).1
  have hzinv : ∀ i, ∀ w ∈ M i, ρ z w ∈ M i := fun i w hw => by
    rw [hMdef, mem_cosetFixed] at hw ⊢
    refine ⟨mapsTo_centralImage (Commute.refl (ρ z)) w hw.1, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, (hzc (x * z ^ (i : ℕ))).eq, map_mul,
      Module.End.mul_apply, hw.2]
  have hM : ∀ i, ∀ e ∈ E, ∀ m ∈ M i, ρ e m ∈ M i := by
    intro i e he m hm
    rw [hMdef, mem_cosetFixed] at hm ⊢
    refine ⟨mapsTo_centralImage ((hzc e).map ρ) m hm.1, ?_⟩
    have hxzE : x * z ^ (i : ℕ) ∈ E := mul_mem hxE (pow_mem hzE _)
    rw [← Module.End.mul_apply, ← map_mul, ← hEcomm e he _ hxzE, map_mul, Module.End.mul_apply,
      hm.2]
  have hMdim : ∀ i, finrank (ZMod 2) (M i) = p - 1 := by
    intro i
    have h := finrank_inf_cosetFixed hp2 hzc hexp' hyx hK hKdim hWdim i
    rw [← hMdef, inf_eq_right.mpr (hWle i)] at h
    exact h
  have hproj : ∀ (j k : Fin p) (w : V), w ∈ M k →
      cosetAverage p ρ z x j w = if (j : ℕ) = k then w else 0 :=
    fun j k w hw => cosetAverage_apply_of_mem hp2 hzc hexp' j.2 k.2 (by rw [← hMdef]; exact hw)
  have hindep : iSupIndep M := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro w ⟨hwi, hwj⟩
    have hker : (⨆ j, ⨆ (_ : j ≠ i), M j) ≤ LinearMap.ker (cosetAverage p ρ z x i) :=
      iSup₂_le fun j hj v hv => by
        rw [LinearMap.mem_ker, hproj i j v hv, ite_eq_right (fun h => hj (Fin.ext h).symm)]
    have h0 := hker hwj
    rw [LinearMap.mem_ker, hproj i i w hwi, ite_eq_left rfl] at h0
    exact (Submodule.mem_bot _).mpr h0
  have hsup : ⨆ i, M i = centralImage ρ z := by
    apply le_antisymm (iSup_le hWle)
    intro w hw
    rw [← sum_cosetAverage_apply (x := x) hp2 hzc hexp' hw, Finset.sum_range]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.mem_iSup_of_mem j (by rw [hMdef]; exact cosetAverage_mem_cosetFixed hzc hexp' j hw)
  have hirr : ∀ i, ∀ S : Submodule (ZMod 2) V, S ≤ M i → (∀ e ∈ E, ∀ s ∈ S, ρ e s ∈ S) →
      S = ⊥ ∨ S = M i := by
    intro i S hSM hS
    by_cases hS0 : S = ⊥
    · exact Or.inl hS0
    right
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    have hle := finrank_centralImageAlgebra_le hK (hSM.trans (hWle i))
      (fun t ht => hS z hzE t ht) hs hs0
    rw [hKdim] at hle
    apply Submodule.eq_of_le_of_finrank_eq hSM
    have := Submodule.finrank_mono hSM
    rw [hMdim i] at this ⊢
    omega
  have hxM : ∀ (i : Fin p) (m : V), m ∈ M i → ρ x m = ρ (z ^ (p - i)) m := by
    intro i m hm
    rw [hMdef] at hm
    have h := (mem_cosetFixed.mp hm).2
    calc ρ x m = ρ (x * z ^ (i : ℕ) * z ^ (p - i)) m := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' i.2.le, hexp' z, mul_one]
      _ = ρ (z ^ (p - i)) (ρ (x * z ^ (i : ℕ)) m) := by
          rw [← Module.End.mul_apply, ← map_mul, ((hzc (x * z ^ (i : ℕ))).pow_right (p - i)).eq]
      _ = ρ (z ^ (p - i)) m := by rw [h]
  have hzM : ∀ (j : Fin p) (n : ℕ), ¬ p ∣ n → ∀ w ∈ M j, ρ (z ^ n) w = w → w = 0 := by
    intro j n hn w hw hfix
    obtain ⟨k, hk⟩ := exists_pow_pow_eq_self (hexp' z) hn
    have hpow : ∀ t : ℕ, ρ ((z ^ n) ^ t) w = w := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, map_mul, Module.End.mul_apply, hfix, ih]
    have hzw : ρ z w = w := by rw [← hk]; exact hpow k
    have hwU : w ∈ centralFixed ρ z := by
      rw [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hzw,
        sub_self]
    have hmem : w ∈ centralFixed ρ z ⊓ centralImage ρ z := ⟨hwU, hWle j hw⟩
    rw [hUW.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  have hnoniso : ∀ i j, i ≠ j → ∀ φ : M i ≃ₗ[ZMod 2] M j, ¬ ∀ (e : Q) (he : e ∈ E) (m : M i),
      φ ⟨ρ e m, hM i e he m m.2⟩ = ⟨ρ e (φ m), hM j e he _ (φ m).2⟩ := by
    intro i j hij φ hφ
    have hMi0 : M i ≠ ⊥ := by
      intro h
      have := hMdim i
      rw [h, finrank_bot] at this
      omega
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMi0
    set w : V := ((φ ⟨m, hm⟩ : M j) : V) with hw
    have hwM : w ∈ M j := (φ ⟨m, hm⟩).2
    have h1 : ρ x w = ρ (z ^ (p - i)) w := by
      have e1 : (⟨ρ x m, hM i x hxE m hm⟩ : M i) =
          ⟨ρ (z ^ (p - (i : ℕ))) m, hM i _ (pow_mem hzE _) m hm⟩ :=
        Subtype.ext (hxM i m hm)
      have h := (hφ x hxE ⟨m, hm⟩).symm.trans ((congrArg φ e1).trans
        (hφ (z ^ (p - (i : ℕ))) (pow_mem hzE _) ⟨m, hm⟩))
      have h' := congrArg Subtype.val h
      exact h'
    have h2 : ρ x w = ρ (z ^ (p - j)) w := hxM j w hwM
    have h3 : ρ (z ^ (p + i - j)) w = w := by
      have e : z ^ (p + (i : ℕ) - j) = z ^ (i : ℕ) * z ^ (p - (j : ℕ)) := by
        rw [← pow_add]
        congr 1
        have := j.2
        omega
      have e' : w = ρ (z ^ (i : ℕ)) (ρ (z ^ (p - (i : ℕ))) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← pow_add, Nat.add_sub_cancel' i.2.le, hexp' z,
          map_one, Module.End.one_apply]
      rw [e, map_mul, Module.End.mul_apply, ← h2, h1, ← e']
    have hnd : ¬ p ∣ p + i - j := by
      rintro ⟨c, hc⟩
      have hi := i.2
      have hj := j.2
      have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      have h1 : p * c < p * 2 := by rw [← hc]; omega
      have h2 : 0 < p * c := by rw [← hc]; omega
      have hc2 : c < 2 := Nat.lt_of_mul_lt_mul_left h1
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at h2
      have hc1 : c = 1 := by omega
      rw [hc1, mul_one] at hc
      omega
    have hw0 := hzM j (p + i - j) hnd w hwM h3
    apply hm0
    have hφ0 : φ ⟨m, hm⟩ = 0 := Subtype.ext hw0
    have h := φ.injective (hφ0.trans (map_zero φ).symm)
    exact congrArg Subtype.val h
  have hself : ∀ i, ∃ B : M i →ₗ[ZMod 2] M i →ₗ[ZMod 2] ZMod 2,
      (∀ a, (∀ b, B a b = 0) → a = 0) ∧ (∀ b, (∀ a, B a b = 0) → b = 0) ∧
      ∀ (e : Q) (he : e ∈ E) (a b : M i),
        B ⟨ρ e a, hM i e he a a.2⟩ ⟨ρ e b, hM i e he b b.2⟩ = B a b := by
    intro i
    have : Finite (centralImage ρ z) := Module.finite_of_finite (ZMod 2)
    have : Finite (Module.End (ZMod 2) (centralImage ρ z)) :=
      Finite.of_injective _ (DFunLike.coe_injective (F := centralImage ρ z →ₗ[ZMod 2] _))
    have : Finite (centralImageAlgebra ρ z) := Subtype.finite
    have hMi0 : M i ≠ ⊥ := by
      intro h
      have := hMdim i
      rw [h, finrank_bot] at this
      omega
    obtain ⟨m₀, hm₀, hm₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMi0
    let w₀ : centralImage ρ z := ⟨m₀, hWle i hm₀⟩
    let Λ : centralImageAlgebra ρ z →ₗ[ZMod 2] M i :=
      { toFun := fun c => ⟨((c : Module.End (ZMod 2) (centralImage ρ z)) w₀ : V),
          apply_mem_of_mem_centralImageAlgebra (hzinv i) c.2 hm₀⟩
        map_add' := fun c d => Subtype.ext (by simp)
        map_smul' := fun r c => Subtype.ext (by simp) }
    have hΛinj : Function.Injective Λ := by
      intro c d hcd
      rw [← sub_eq_zero]
      by_contra hne
      obtain ⟨u, hu⟩ := hK.mul_inv_cancel hne
      apply hm₀0
      have h0 : ((c - d : centralImageAlgebra ρ z) : Module.End (ZMod 2) (centralImage ρ z)) w₀
          = 0 := by
        rw [Subalgebra.coe_sub, LinearMap.sub_apply, sub_eq_zero]
        have h := congrArg Subtype.val hcd
        exact Subtype.ext h
      have hu' : u * (c - d) = 1 := by
        rw [hK.mul_comm]
        exact hu
      have h1 : ((u * (c - d) : centralImageAlgebra ρ z) :
          Module.End (ZMod 2) (centralImage ρ z)) w₀ = w₀ := by
        rw [hu', Subalgebra.coe_one, Module.End.one_apply]
      rw [Subalgebra.coe_mul, Module.End.mul_apply, h0, map_zero] at h1
      have h2 := congrArg Subtype.val h1
      exact h2.symm
    have : Module.Finite (ZMod 2) (centralImageAlgebra ρ z) := Module.Finite.of_finite
    have hKcard : Nat.card (centralImageAlgebra ρ z) = 2 ^ (p - 1) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hKdim, Nat.card_zmod]
    have : Finite (M i) := Module.finite_of_finite (ZMod 2)
    have hMcard : Nat.card (M i) = 2 ^ (p - 1) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hMdim i, Nat.card_zmod]
    have hΛsurj : Function.Surjective Λ :=
      (hΛinj.bijective_of_nat_card_le (by rw [hKcard, hMcard])).2
    set L := LinearEquiv.ofBijective Λ ⟨hΛinj, hΛsurj⟩ with hL
    have hLapp : ∀ c, L c = Λ c := fun _ => rfl
    have hkey : ∀ (e : Q) (he : e ∈ E) (α : centralImageAlgebra ρ z),
        ρ e ((Λ α : M i) : V) = ((Λ (α * L.symm ⟨ρ e m₀, hM i e he m₀ hm₀⟩) : M i) : V) := by
      intro e he α
      set κ := L.symm ⟨ρ e m₀, hM i e he m₀ hm₀⟩ with hκ
      let Ae : Module.End (ZMod 2) (centralImage ρ z) :=
        (ρ e).restrict (mapsTo_centralImage ((hzc e).map ρ))
      have hAe : Commute Ae (centralImageOp ρ z) := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ρ e (ρ z w) = ρ z (ρ e w)
        rw [← Module.End.mul_apply, ← map_mul, (hzc e).eq, map_mul, Module.End.mul_apply]
      have hcomm := (commute_of_mem_centralImageAlgebra hAe α.2).eq
      have hAew₀ : Ae w₀ = (κ : Module.End (ZMod 2) (centralImage ρ z)) w₀ := by
        have hLκ : L κ = ⟨ρ e m₀, hM i e he m₀ hm₀⟩ := L.apply_symm_apply _
        apply Subtype.ext
        have h := congrArg Subtype.val hLκ
        exact h.symm
      have hW : (Ae * (α : Module.End (ZMod 2) (centralImage ρ z))) w₀ =
          ((α * κ : centralImageAlgebra ρ z) : Module.End (ZMod 2) (centralImage ρ z)) w₀ := by
        rw [hcomm, Module.End.mul_apply, hAew₀, Subalgebra.coe_mul, Module.End.mul_apply]
      have h := congrArg Subtype.val hW
      exact h
    have hact : ∀ (e : Q) (he : e ∈ E) (a : M i),
        L.symm ⟨ρ e a, hM i e he a a.2⟩ = L.symm ⟨ρ e m₀, hM i e he m₀ hm₀⟩ * L.symm a := by
      intro e he a
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      have h := hkey e he (L.symm a)
      rw [← hLapp (L.symm a), LinearEquiv.apply_symm_apply] at h
      rw [hK.mul_comm]
      exact h
    have hΛone : ((Λ 1 : M i) : V) = m₀ := rfl
    have hκpow : ∀ (e : Q) (he : e ∈ E), (L.symm ⟨ρ e m₀, hM i e he m₀ hm₀⟩) ^ p = 1 := by
      intro e he
      set κ := L.symm ⟨ρ e m₀, hM i e he m₀ hm₀⟩ with hκ
      have hpowe : ∀ n : ℕ, ρ (e ^ n) m₀ = ((Λ (κ ^ n) : M i) : V) := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, hΛone]
        | succ n ih =>
          rw [pow_succ', map_mul, Module.End.mul_apply, ih, hkey e he, pow_succ, ← hκ]
      have h1 := hpowe p
      rw [hexp' e, map_one, Module.End.one_apply, ← hΛone] at h1
      exact hΛinj (Subtype.ext h1.symm)
    have hκq : ∀ (e : Q) (he : e ∈ E),
        (L.symm ⟨ρ e m₀, hM i e he m₀ hm₀⟩) ^ (2 ^ ((p - 1) / 2) + 1) = 1 := by
      intro e he
      obtain ⟨t, ht⟩ := dvd_two_pow_half_add_one hp2 hord
      rw [ht, pow_mul, hκpow e he, one_pow]
    let _ : Field (centralImageAlgebra ρ z) := hK.toField
    obtain ⟨B₀, hB₀l, hB₀r, hB₀inv⟩ :=
      exists_nondegenerate_bilin_frobenius_invariant (K := centralImageAlgebra ρ z) ((p - 1) / 2)
    refine ⟨B₀.compl₁₂ L.symm.toLinearMap L.symm.toLinearMap, ?_, ?_, ?_⟩
    · intro a ha
      have h : L.symm a = 0 := hB₀l _ fun β => by
        have h' := ha (L β)
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply] at h'
        exact h'
      rw [← L.apply_symm_apply a, h, map_zero]
    · intro b hb
      have h : L.symm b = 0 := hB₀r _ fun α => by
        have h' := hb (L α)
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply] at h'
        exact h'
      rw [← L.apply_symm_apply b, h, map_zero]
    · intro e he a b
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
      rw [hact e he a, hact e he b]
      exact hB₀inv _ (hκq e he) _ _
  exact ⟨M, hM, hindep, hsup, hMdim, hirr, hnoniso, hself⟩

end CFSG.RankThree.GroupTheory.SteinbergBM
