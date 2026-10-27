module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec10.Item1012Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_thetaComponentsIn {H K : Subgroup G} (hK : K ∈ thetaComponentsIn H) {n : G}
    (hn : n ∈ H) : K.map (MulAut.conj n).toMonoidHom ∈ thetaComponentsIn H := by
  obtain ⟨L, hL, rfl⟩ := hK
  refine ⟨L.map (MulAut.conj (⟨n, hn⟩ : H)).toMonoidHom,
    map_mulEquiv_mem_thetaComponents Nat.prime_three _ hL, ?_⟩
  dsimp only
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem commutator_mem_theta_of_ne {H : Type} [Group H] [Finite H] {L₁ L₂ : Subgroup H}
    (h₁ : L₁ ∈ thetaComponents 3 H) (h₂ : L₂ ∈ thetaComponents 3 H) (hne : L₁ ≠ L₂) {x y : H}
    (hx : x ∈ L₁) (hy : y ∈ L₂) : ⁅x, y⁆ ∈ aschbacherSolvableCore 3 H := by
  set N := aschbacherSolvableCore 3 H with hN
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hK₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₁
  have hK₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₂
  have hKne : L₁.map (QuotientGroup.mk' N) ≠ L₂.map (QuotientGroup.mk' N) := fun h =>
    hne (hbij.injOn h₁ h₂ h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  have h1 : ⁅QuotientGroup.mk' N x, QuotientGroup.mk' N y⁆ ∈
      ⁅L₁.map (QuotientGroup.mk' N), L₂.map (QuotientGroup.mk' N)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hx)
      (Subgroup.mem_map_of_mem _ hy)
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement] at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

omit [Finite G] in
theorem card_autIn_dvd (T S : Subgroup G) : Nat.card (Sec4.autIn T S) ∣ Nat.card T := by
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : T ⊓ Subgroup.normalizer (S : Set G) ≤ _)).toEquiv]
  exact Subgroup.card_dvd_of_le inf_le_left

omit [Finite G] in
theorem card_autIn_mul_card_inf_centralizer (K S : Subgroup G) :
    Nat.card (Sec4.autIn K S) *
        Nat.card (K ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) =
      Nat.card (K ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) := by
  set N := Subgroup.normalizer (S : Set G) with hN
  set U := K ⊓ N with hU
  set f : U →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right) with hf
  have hrange : f.range = Sec4.autIn K S := by
    ext σ
    rw [MonoidHom.mem_range, Sec4.mem_autIn_iff]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2.2, u.2.1, rfl⟩
    · rintro ⟨g, hgN, hgK, rfl⟩
      exact ⟨⟨g, hgK, hgN⟩, rfl⟩
  have hCU : K ⊓ Subgroup.centralizer (S : Set G) ≤ U :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hker : f.ker = (K ⊓ Subgroup.centralizer (S : Set G)).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨u.2.1, h⟩, fun h => h.2⟩
  have hcardker : Nat.card f.ker =
      Nat.card (K ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
  rw [← hrange, ← hcardker, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

omit [Finite G] in
theorem not_three_dvd_card_inf_centralizer {K S : Subgroup G}
    (h27 : 27 ∣ Nat.card (Sec4.autIn K S)) (h81 : ¬ 81 ∣ Nat.card K) :
    ¬ 3 ∣ Nat.card (K ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) := by
  intro h3
  apply h81
  have h1 : 81 ∣ Nat.card (K ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) := by
    rw [← card_autIn_mul_card_inf_centralizer K S]
    exact (show (81 : ℕ) = 27 * 3 by norm_num) ▸ Nat.mul_dvd_mul h27 h3
  exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)

theorem not_dvd_card_of_type {K : Subgroup G}
    (htype : Sec4.IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) 4 ∨
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) :
    ¬ 81 ∣ Nat.card K := by
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hq : Nat.card (K ⧸ aschbacherSolvableCore 3 K) = 60480 ∨
      Nat.card (K ⧸ aschbacherSolvableCore 3 K) = 1080 := by
    rcases htype with h4 | h6
    · exact Or.inl (Step1012ClaimProof.card_of_isSLThreePiAt_four h4)
    · exact Or.inr (KFacts.KS14.card_eq_of_isExtOf_alternating_six h6.isExtOf)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 K)]
  intro h81
  have hcop : Nat.Coprime 81 (Nat.card (aschbacherSolvableCore 3 K)) := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ)
  have h := hcop.dvd_of_dvd_mul_right h81
  rcases hq with hq | hq <;> rw [hq] at h <;> norm_num at h

theorem mem_normalizer_of_le_autIn {H K S : Subgroup G} (hK : K ∈ thetaComponentsIn H)
    (hcov : inSubgroup perfectResidual (Sec4.autIn H S) ≤ Sec4.autIn K S)
    (h3 : 3 ∣ Nat.card (inSubgroup perfectResidual (Sec4.autIn H S)))
    {n : G} (hnH : n ∈ H) (hnS : n ∈ Subgroup.normalizer (S : Set G)) :
    n ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hnK
  set X := Sec4.autIn H S with hX
  set Xinf := inSubgroup perfectResidual X with hXinf
  set K' := K.map (MulAut.conj n).toMonoidHom with hK'
  have hK'mem : K' ∈ thetaComponentsIn H := conj_mem_thetaComponentsIn hK hnH
  obtain ⟨hKH, hKθ⟩ := mem_thetaComponentsIn_iff.mp hK
  obtain ⟨hK'H, hK'θ⟩ := mem_thetaComponentsIn_iff.mp hK'mem
  have hne : K.subgroupOf H ≠ K'.subgroupOf H := by
    intro heq
    apply hnK
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hKH, inf_eq_left.mpr hK'H] at heq
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
  set Θ := inSubgroup (aschbacherSolvableCore 3) H with hΘ
  have hcomm : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ Θ := by
    intro x hx y hy
    have h1 := commutator_mem_theta_of_ne hKθ hK'θ hne (x := ⟨x, hKH hx⟩) (y := ⟨y, hK'H hy⟩)
      (Subgroup.mem_subgroupOf.mpr hx) (Subgroup.mem_subgroupOf.mpr hy)
    exact ⟨_, h1, rfl⟩
  set ν := S.normalizerMonoidHom ⟨n, hnS⟩ with hν
  have hnX : ν ∈ X := Sec4.mem_autIn_iff.mpr ⟨n, hnS, hnH, rfl⟩
  have hcov' : Xinf ≤ Sec4.autIn K' S := by
    intro τ hτ
    have hτ' : ν⁻¹ * τ * ν⁻¹⁻¹ ∈ Xinf :=
      GroupTheory.conj_mem_inSubgroup_perfectResidual (X.inv_mem hnX) hτ
    rw [inv_inv] at hτ'
    obtain ⟨k, hkN, hkK, hk⟩ := Sec4.mem_autIn_iff.mp (hcov hτ')
    have hnkN : n * k * n⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hnS hkN) (Subgroup.inv_mem _ hnS)
    refine Sec4.mem_autIn_iff.mpr ⟨n * k * n⁻¹, hnkN, ⟨k, hkK, rfl⟩, ?_⟩
    have hsplit : (⟨n * k * n⁻¹, hnkN⟩ : Subgroup.normalizer (S : Set G)) =
        ⟨n, hnS⟩ * ⟨k, hkN⟩ * (⟨n, hnS⟩)⁻¹ := rfl
    rw [hsplit, map_mul, map_mul, map_inv, hk, ← hν]
    group
  have hperf : Group.IsPerfect Xinf :=
    isPerfect_map_subtype (perfect_residual_characterization (G := X)).2.2.1
  have hle : Xinf ≤ Sec4.autIn Θ S := by
    rw [← Subgroup.commutator_eq_self (H := Xinf), Subgroup.commutator_le]
    intro σ hσ τ hτ
    obtain ⟨x, hxN, hxK, rfl⟩ := Sec4.mem_autIn_iff.mp (hcov hσ)
    obtain ⟨y, hyN, hyK', rfl⟩ := Sec4.mem_autIn_iff.mp (hcov' hτ)
    have hxyN : ⁅x, y⁆ ∈ Subgroup.normalizer (S : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hyN)
        (Subgroup.inv_mem _ hxN)) (Subgroup.inv_mem _ hyN)
    refine Sec4.mem_autIn_iff.mpr ⟨⁅x, y⁆, hxyN, hcomm x hxK y hyK', ?_⟩
    rw [← map_commutatorElement]
    rfl
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    rw [hΘ, inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  exact hΘ3 (h3.trans ((Subgroup.card_dvd_of_le hle).trans (card_autIn_dvd Θ S)))

omit [Finite G] in
theorem pow_mul_inv_pow_mem {K : Subgroup G} {c k : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) (n : ℕ) :
    (k⁻¹ * c) ^ n * (c ^ n)⁻¹ ∈ K := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hconj : c ^ n * k⁻¹ * (c ^ n)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hc n) _).mp (K.inv_mem hk)
    have heq : (k⁻¹ * c) ^ (n + 1) * (c ^ (n + 1))⁻¹ =
        ((k⁻¹ * c) ^ n * (c ^ n)⁻¹) * (c ^ n * k⁻¹ * (c ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [heq]
    exact K.mul_mem ih hconj

omit [Finite G] in
theorem exists_eq_mul_of_mem_normalizer {K C Z : Subgroup G} {c k : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) (hyC : k⁻¹ * c ∈ C)
    (hc3 : c ^ 3 = 1) (hKC : ¬ 3 ∣ Nat.card (K ⊓ C : Subgroup G))
    (hZ : ∀ x ∈ C, x ^ 3 = 1 → x ∈ Z) : ∃ k' ∈ K, ∃ z ∈ Z, c = k' * z := by
  set y := k⁻¹ * c with hy
  have hy3K : y ^ 3 ∈ K := by
    have h := pow_mul_inv_pow_mem hc hk 3
    rwa [hc3, inv_one, mul_one] at h
  have hy3C : y ^ 3 ∈ C := C.pow_mem hyC 3
  set m := orderOf (y ^ 3) with hm
  have hm3 : ¬ 3 ∣ m := by
    intro h3
    apply hKC
    have h1 := orderOf_dvd_natCard (⟨y ^ 3, hy3K, hy3C⟩ : (K ⊓ C : Subgroup G))
    rw [← Subgroup.orderOf_coe] at h1
    exact h3.trans h1
  have hmm : m * m % 3 = 1 := by
    have h : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rw [Nat.mul_mod]
    rcases h with h | h <;> rw [h]
  obtain ⟨t, ht⟩ : ∃ t, m * m = 3 * t + 1 := ⟨m * m / 3, by omega⟩
  refine ⟨k * ((y ^ 3) ^ t)⁻¹, K.mul_mem hk (K.inv_mem (K.pow_mem hy3K t)), y ^ (m * m),
    hZ _ (C.pow_mem hyC _) ?_, ?_⟩
  · rw [← pow_mul, show m * m * 3 = 3 * m * m by ring, pow_mul, pow_mul, hm,
      pow_orderOf_eq_one, one_pow]
  · rw [ht, pow_succ y (3 * t), pow_mul y 3 t, mul_assoc, inv_mul_cancel_left, hy,
      mul_inv_cancel_left]

omit [Finite G] in
theorem inv_mul_conj_mem_of_eq_mul {K : Subgroup G} {c w k' z : G}
    (hw : w ∈ Subgroup.normalizer (K : Set G)) (hk' : k' ∈ K) (hc : c = k' * z)
    (hzw : z * w = w * z) (hzK : ∀ x ∈ K, z * x = x * z) : c⁻¹ * (w * c * w⁻¹) ∈ K := by
  have hwk : w * k' * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hw k').mp hk'
  have hmem : k'⁻¹ * (w * k' * w⁻¹) ∈ K := K.mul_mem (K.inv_mem hk') hwk
  have hzw' : z * w⁻¹ = w⁻¹ * z := ((show Commute z w from hzw).inv_right).eq
  have heq : c⁻¹ * (w * c * w⁻¹) = z⁻¹ * ((k'⁻¹ * (w * k' * w⁻¹)) * z) := by
    calc c⁻¹ * (w * c * w⁻¹) = z⁻¹ * k'⁻¹ * w * k' * (z * w⁻¹) := by rw [hc]; group
      _ = z⁻¹ * ((k'⁻¹ * (w * k' * w⁻¹)) * z) := by rw [hzw']; group
  rw [heq, ← hzK _ hmem, inv_mul_cancel_left]
  exact hmem

end CFSG.RankThree.PartTwo.Sec10.Item1012Res2Proof
