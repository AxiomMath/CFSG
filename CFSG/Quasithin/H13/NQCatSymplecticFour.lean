module

public import CFSG.Quasithin.H13.NQCatInputs
public import CFSG.Quasithin.SteinbergBTSymplecticThreeFreeTriangular
public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.Quasithin.H13.NQTerm CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise commutatorElement

theorem threeFreeBorelDatum_of_mulEquiv {C C' : Type*} [Group C] [Group C'] {U B : Subgroup C}
    (h : ThreeFreeBorelDatum U B) (e : C ≃* C') :
    ThreeFreeBorelDatum (U.map e.toMonoidHom) (B.map e.toMonoidHom) where
  le := map_mono h.le
  commutator_le := by
    rw [← map_commutator]
    exact map_mono h.commutator_le
  normalizer_le := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono h.normalizer_le
  isPGroup := h.isPGroup.map _
  three_free D hUD h3 := by
    have hD : D = (D.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [map_map]
      ext x
      simp
    rw [hD]
    refine map_mono (h.three_free _ ?_ ?_)
    · have := map_mono (f := e.symm.toMonoidHom) hUD
      rwa [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id C from
        MonoidHom.ext fun x => by simp, map_id] at this
    · rwa [card_map_of_injective e.symm.injective]

theorem threeFreeBorelDatum_statedSp (hleaf : EvenSymplecticThreeFreeSylowOvergroupsTriangular)
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ThreeFreeBorelDatum (unipotent 2 K) (borelSubgroup 2 K) where
  le := unipotent_le_borelSubgroup
  commutator_le := by
    obtain ⟨-, -, -, -, hker, -⟩ := symplectic_higher_triangular_structure (r := 2) (K := K)
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h : diagHom 2 K ⁅(⟨g₁, hg₁⟩ : borelSubgroup 2 K), ⟨g₂, hg₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    have h' : ⁅(⟨g₁, hg₁⟩ : borelSubgroup 2 K), ⟨g₂, hg₂⟩⁆ ∈
        (unipotent 2 K).subgroupOf (borelSubgroup 2 K) := by
      rw [← hker]
      exact h
    rw [mem_subgroupOf] at h'
    simpa [commutatorElement_def] using h'
  normalizer_le := (hleaf K 2 (by norm_num)).2.le
  isPGroup := by
    obtain ⟨-, -, -, -, ⟨P, hP⟩, -⟩ :=
      symplectic_higher_order_and_Sylow (K := K) 2 (Nat.card K) rfl (r := 2) (by norm_num)
    rw [← hP]
    exact P.isPGroup'
  three_free := (hleaf K 2 (by norm_num)).1

theorem card_ker_powMonoidHom_dvd {X : Type*} [CommGroup X] [Finite X] [IsCyclic X] (p : ℕ) :
    Nat.card (powMonoidHom p : X →* X).ker ∣ p := by
  set W := (powMonoidHom p : X →* X).ker
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun w => Subtype.ext ?_
  have := w.2
  rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
  rw [Subgroup.coe_pow, this, Subgroup.coe_one]

theorem evenSymplecticThreeFreeSylowOvergroupsTriangular :
    EvenSymplecticThreeFreeSylowOvergroupsTriangular := fun K _ _ _ r _ =>
  SteinbergBT.even_symplectic_three_free_sylow_overgroups_are_triangular (r := r) (K := K)

theorem even_symplectic_four_common_sylow_odd_subgroup_normalizer_action_is_cyclic
    {f : ℕ} (hf : 2 ≤ f)
    (k : Type) [Field k] (hk : Nat.card k = 2 ^ f) (U : Sylow 2 (StatedProj (StatedSp 2 k)))
    (A : Subgroup (StatedProj (StatedSp 2 k))) (hAodd : Odd (Nat.card A))
    (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set (StatedProj (StatedSp 2 k))) * (U : Set (StatedProj (StatedSp 2 k))) =
      (U : Set (StatedProj (StatedSp 2 k))) * (A : Set (StatedProj (StatedSp 2 k)))) :
    (∃ φ : A →* kˣ × kˣ, Function.Injective φ) ∧
    (∀ α ∈ pairAutSubgroup A (U : Subgroup (StatedProj (StatedSp 2 k))) ⊓
        (MulAut.conj : StatedProj (StatedSp 2 k) →* MulAut (StatedProj (StatedSp 2 k))).range,
      ∀ a ∈ A, α a = a) ∧
    (IsCyclic (pairAutRestrict A (U : Subgroup (StatedProj (StatedSp 2 k)))).range ∧
      Nat.card (pairAutRestrict A (U : Subgroup (StatedProj (StatedSp 2 k)))).range ∣ 2 * f) ∧
    (∀ Δ : Subgroup (pairAutSubgroup A (U : Subgroup (StatedProj (StatedSp 2 k)))),
      IsCyclic (Δ.map (pairAutRestrict A (U : Subgroup (StatedProj (StatedSp 2 k))))) ∧
        Nat.card (Δ.map (pairAutRestrict A (U : Subgroup (StatedProj (StatedSp 2 k))))) ∣
          2 * f) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ IsCyclic A → Monoid.exponent A = p →
      p ∣ 2 ^ f - 1 ∧ IsElementaryAbelian p A ∧ Nat.card A = p ^ 2) := by
  classical
  have hleaf := evenSymplecticThreeFreeSylowOvergroupsTriangular
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1 hk
  have hbij := (LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
    (r := 2) (K := k) hf1 hk).1
  let π : StatedSp 2 k ≃* StatedProj (StatedSp 2 k) := MulEquiv.ofBijective (proj 2 k) hbij
  have hπ : π.toMonoidHom = proj 2 k := MonoidHom.ext fun _ => rfl
  have hdat₀ := threeFreeBorelDatum_of_mulEquiv (threeFreeBorelDatum_statedSp hleaf k) π
  obtain ⟨-, -, -, -, -, -, ⟨P₀, hP₀⟩, -⟩ :=
    symplectic_higher_order_and_Sylow (K := k) 2 (Nat.card k) rfl (r := 2) (by norm_num)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 k)) P₀ U
  have hUc : (U : Subgroup (StatedProj (StatedSp 2 k))) =
      ((unipotent 2 k).map π.toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, coe_smul_sylow_eq_map, hP₀, hπ]
    rfl
  have hdat := hdat₀.map (MulAut.conj c)
  rw [← hUc] at hdat
  obtain ⟨hAB, hAU', hcomm, hfix⟩ := hdat.commute_of_permutable A hAodd hA3 hAU
  have hAB' : ∀ a ∈ A, π.symm (c⁻¹ * a * c) ∈ borelSubgroup 2 k := by
    intro a ha
    obtain ⟨b, ⟨b', hb', rfl⟩, hb⟩ := hAB ha
    have hb'' : c⁻¹ * a * c = π b' := by
      rw [← hb]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hb'', MulEquiv.symm_apply_apply]
    exact hb'
  let ψ : A →* borelSubgroup 2 k :=
    ((π.symm.toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom).comp A.subtype).codRestrict _
      fun a => by
        have := hAB' a a.2
        simpa [MulAut.conj_apply] using this
  let φ : A →* kˣ × kˣ :=
    ((Pi.evalMonoidHom (fun _ : Fin 2 => kˣ) 0).comp ((diagHom 2 k).comp ψ)).prod
      ((Pi.evalMonoidHom (fun _ : Fin 2 => kˣ) 1).comp ((diagHom 2 k).comp ψ))
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : diagHom 2 k (ψ a) = 1 := by
      have h0 := congrArg Prod.fst ha
      have h1' := congrArg Prod.snd ha
      funext i
      fin_cases i
      · exact h0
      · exact h1'
    obtain ⟨-, -, -, -, hker, -⟩ := symplectic_higher_triangular_structure (r := 2) (K := k)
    have h2 : ψ a ∈ (unipotent 2 k).subgroupOf (borelSubgroup 2 k) := by
      rw [← hker]
      exact h1
    rw [mem_subgroupOf] at h2
    have h3 : (a : StatedProj (StatedSp 2 k)) ∈ (U : Subgroup (StatedProj (StatedSp 2 k))) := by
      rw [hUc]
      refine ⟨π ((ψ a : borelSubgroup 2 k) : StatedSp 2 k), ⟨_, h2, rfl⟩, ?_⟩
      simp [ψ, MulAut.conj_apply, mul_assoc]
    have h4 : (a : StatedProj (StatedSp 2 k)) ∈ A ⊓ (U : Subgroup _) := ⟨a.2, h3⟩
    rw [hAU', mem_bot] at h4
    exact Subtype.ext h4
  have hinner : ∀ α ∈ pairAutSubgroup A (U : Subgroup (StatedProj (StatedSp 2 k))) ⊓
      (MulAut.conj : StatedProj (StatedSp 2 k) →* MulAut (StatedProj (StatedSp 2 k))).range,
        ∀ a ∈ A, α a = a := by
    rintro α ⟨hαΓ, g, rfl⟩ a ha
    exact hfix g (mem_normalizer_of_map_conj_eq hαΓ.2) (mem_normalizer_of_map_conj_eq hαΓ.1) a ha
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ :=
    ComponentClassification.UnbalancedCatalog.even_symplectic_two_exterior_square_automorphism
      hf1 hk
  obtain ⟨-, -, -, -, -, -, hcycOut, hcardOut, -⟩ := hall γ hγ
  have : Finite (Outer (StatedProj (StatedSp 2 k))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardOut]; omega)
  set Γ := pairAutSubgroup A (U : Subgroup (StatedProj (StatedSp 2 k)))
  set ρ := pairAutRestrict A (U : Subgroup (StatedProj (StatedSp 2 k)))
  let Θ : MulAut (StatedProj (StatedSp 2 k)) →* Outer (StatedProj (StatedSp 2 k)) :=
    QuotientGroup.mk' _
  have hker : (Θ.comp Γ.subtype).ker ≤ ρ.ker := by
    intro α hα
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hα
    have hαI : (α : MulAut (StatedProj (StatedSp 2 k))) ∈
        ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 k)) :=
      (QuotientGroup.eq_one_iff _).1 hα
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    exact hinner α ⟨α.2, hαI⟩ x x.2
  have hΔ := map_isCyclic_of_ker_le (Θ.comp Γ.subtype) ρ hker
  rw [hcardOut] at hΔ
  refine ⟨⟨φ, hφinj⟩, hinner, ?_, hΔ, fun p hp hp5 hnc hexp => ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact hΔ ⊤
  have : Fact p.Prime := ⟨hp⟩
  set W := (powMonoidHom p : kˣ →* kˣ).ker with hWdef
  have hWp : Nat.card W ∣ p := card_ker_powMonoidHom_dvd p
  have hφW : φ.range ≤ W.prod W := by
    rintro _ ⟨a, rfl⟩
    have hap : a ^ p = 1 := by
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one a
    have h := congrArg φ hap
    rw [map_pow, map_one] at h
    refine ⟨?_, ?_⟩
    · change (φ a).1 ∈ (powMonoidHom p : kˣ →* kˣ).ker
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      simpa using congrArg Prod.fst h
    · change (φ a).2 ∈ (powMonoidHom p : kˣ →* kˣ).ker
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      simpa using congrArg Prod.snd h
  have hcardA : Nat.card A = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
  have hrange : Nat.card φ.range ∣ p ^ 2 := by
    refine (card_dvd_of_le hφW).trans ?_
    rw [Nat.card_congr (Subgroup.prodEquiv W W).toEquiv, Nat.card_prod, sq]
    exact Nat.mul_dvd_mul hWp hWp
  obtain ⟨j, hj, hjA⟩ := (Nat.dvd_prime_pow hp).1 hrange
  have hj2 : j = 2 := by
    by_contra hj2
    have hj1 : j = 0 ∨ j = 1 := by omega
    apply hnc
    rcases hj1 with rfl | rfl
    · rw [pow_zero] at hjA
      have : Subsingleton A := by
        rw [← Finite.card_le_one_iff_subsingleton, hcardA, hjA]
      infer_instance
    · exact isCyclic_of_prime_card (hcardA.trans (hjA.trans (pow_one p)))
  subst hj2
  have hel : IsElementaryAbelian p A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
      exponent_dvd_p := hexp.dvd }
  refine ⟨?_, hel, hcardA.trans hjA⟩
  by_contra hpd
  have hkx : Nat.card kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hk]
  have hcop : Nat.Coprime p (2 ^ f - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpd
  have hW1 : Nat.card W = 1 := by
    have h := Nat.dvd_gcd hWp
      (show Nat.card W ∣ 2 ^ f - 1 from hkx ▸ card_subgroup_dvd_card W)
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact Nat.dvd_one.1 h
  have h1 : Nat.card φ.range ∣ 1 := by
    have := card_dvd_of_le hφW
    rwa [Nat.card_congr (Subgroup.prodEquiv W W).toEquiv, Nat.card_prod, hW1] at this
  rw [hjA] at h1
  have h25 : 25 ≤ p ^ 2 := by nlinarith
  have := Nat.le_of_dvd one_pos h1
  omega

end CFSG.Quasithin.H13.NQCat
