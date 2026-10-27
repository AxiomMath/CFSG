module

public import CFSG.RankThree.PartOne.F106.OddRadTools
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenCyclotomicFourActors
public import CFSG.RankThree.PartOne.S11c.Sec66F4
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourNonregular

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.EvenF4Actors CFSG.RankThree.PartOne.Sec66T
open CFSG.LieType.Ree (ReeTag)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem odd_card_radical_residual_of_odd_card {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    (h : Odd (Nat.card ↥Y)) : Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥Y))) := by
  have h1 : Nat.card ↥(solvableRadical ↥(perfectResidual ↥Y)) ∣ Nat.card ↥(perfectResidual ↥Y) :=
    Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card ↥(perfectResidual ↥Y) ∣ Nat.card ↥Y := Subgroup.card_subgroup_dvd_card _
  exact Odd.of_dvd_nat h (h1.trans h2)

theorem simple_perfect_commutator_of_map_eq {G M : Type*} [Group G] [Group M] {ι : G →* M}
    {ψ : M →* M} (hι : Function.Injective ι) (hψ : Function.Injective ψ) {X : Subgroup G}
    {D : Subgroup M} (hmap : ⁅X, X⁆.map ι = ⁅D, D⁆.map ψ) (hs : IsSimpleGroup ↥⁅D, D⁆)
    (hnc : ∃ a b : ↥⁅D, D⁆, a * b ≠ b * a) :
    IsSimpleGroup ↥⁅X, X⁆ ∧ Group.IsPerfect ↥⁅X, X⁆ := by
  let e : ↥⁅X, X⁆ ≃* ↥⁅D, D⁆ :=
    ((Subgroup.equivMapOfInjective ⁅X, X⁆ ι hι).trans (MulEquiv.subgroupCongr hmap)).trans
      (Subgroup.equivMapOfInjective ⁅D, D⁆ ψ hψ).symm
  have hsX : IsSimpleGroup ↥⁅X, X⁆ := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnc
  have hncX : ∃ a b : ↥⁅X, X⁆, a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact ⟨hsX, isPerfect_of_simple_nonabelian hncX⟩

theorem oddRad_F4_two_aux {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω)
    (hF : ∀ c, F c = c ^ Nat.card K) (x : adjointGroup .F4 K) (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Subgroup.centralizer {x})))) := by
  classical
  have hp5 : (5 : ℕ).Prime := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpd : 5 ∣ Nat.card K ^ 2 + 1 := by
    rw [hK]
    norm_num
  obtain ⟨g, hg, hgn⟩ := (F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF _ rfl).1
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Subgroup (ModGL .F4 Ω), Γ = conjEntrywiseImage K g⁻¹ := ⟨_, rfl⟩
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subgroup (ModGL .F4 Ω), T₀ = torusGroup .F4 Ω ⊓ Γ := ⟨_, rfl⟩
  have hP : IsPGroup 5 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := EvenF4CyclotomicFourActors.exists_conj_mem_torus K hp5 (by norm_num) hpd Ω F
    hF _ g rfl hg hgn Γ T₀ hΓ hT₀ _ hP
  obtain ⟨x', hx'⟩ : ∃ x' : ModGL .F4 Ω, x' = g⁻¹ * baseChangeGL (algebraMap K Ω)
      ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * g := ⟨_, rfl⟩
  have hx'T₀ : x' ∈ T₀ := hx' ▸ hc x (Subgroup.mem_zpowers x)
  have hx₁ord : orderOf (c * x * c⁻¹) = 5 := by
    rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj c).injective, hx]
  have hx'ord : orderOf x' = 5 := by
    have h1 : x' = (MulAut.conj g⁻¹) (baseChangeGL (algebraMap K Ω)
        ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K)) := by
      rw [hx', MulAut.conj_apply, inv_inv]
    have h2 : orderOf (baseChangeGL (algebraMap K Ω)
        ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K)) = 5 := by
      have := orderOf_injective ((baseChangeGL (algebraMap K Ω)).comp
        (adjointGroup .F4 K).subtype)
        ((baseChangeGL_injective (τ := .F4) (algebraMap K Ω)).comp Subtype.val_injective)
        (c * x * c⁻¹)
      simpa [hx₁ord] using this
    rw [h1, ← MulEquiv.coe_toMonoidHom, orderOf_injective _ (MulAut.conj g⁻¹).injective, h2]
  by_cases hne : {α | IsRoot .F4 α ∧ torusRootChar x' α = 1}.Nonempty
  swap
  · exact odd_card_radical_residual_of_odd_card _
      (EvenF4CyclotomicFourActors.odd_centralizer_of_empty_kernel K hp5 (by norm_num) hpd Ω F hF
        _ g rfl hg hgn Γ T₀ hΓ hT₀ x c hx x' hx' hx'T₀ (Set.not_nonempty_iff_eq_empty.1 hne))
  have hf1 : 1 ≤ 1 := le_rfl
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨K₄, hK₄⟩ := exists_intermediateField_finrank K Ω 4
  have : FiniteDimensional K K₄ := Module.finite_of_finrank_eq_succ hK₄
  have : Finite K₄ := Module.finite_of_finite K
  obtain ⟨-, hCA⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF _ rfl
  obtain ⟨-, -, -, hprime, -⟩ := hCA g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨-, -, -, hdich⟩ := hprime 5 hp5 (by norm_num) hpd
  obtain ⟨hcases, -, -⟩ := hdich x' hx'T₀ hx'ord _ rfl
  obtain ⟨u, ε, hε, hu, huw⟩ := hcases.resolve_left (Set.nonempty_iff_ne_empty.1 hne)
  obtain ⟨-, Z₀, P, -, hZ₀odd, -, -, hcenter, h4, h2, -, -, hcent, x₀, hx₀, hCx, R₀, hR₀, k, hk,
    hRk⟩ := even_F4_cyclotomic_four_nonregular_derived_centralizer hf1 K hK' Ω F hF hp5
      (by norm_num) K₄ hK₄ _ g rfl hg hgn Γ T₀ hΓ hT₀ x' hx'T₀ hx'ord u ε hε hu huw _ _ rfl rfl
      _ _ _ rfl rfl rfl
  obtain ⟨-, -, hsimp, -, r₁, r₂, hr⟩ := h2 hK
  have hx₀x : x₀ = c * x * c⁻¹ := by
    apply Subtype.ext
    apply baseChangeGL_injective (τ := .F4) (algebraMap K Ω)
    rw [hx₀, hx']
    group
  subst hx₀x
  have hι : Function.Injective
      ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) :=
    (baseChangeGL_injective (τ := .F4) (algebraMap K Ω)).comp Subtype.val_injective
  obtain ⟨hmap, -, -, -⟩ := transport_derived hι (MulAut.conj _).injective hCx
  obtain ⟨hs', hp'⟩ := simple_perfect_commutator_of_map_eq hι (MulAut.conj _).injective hmap hsimp
    ⟨r₁, r₂, hr⟩
  have hodd := odd_card_radical_residual_of_dichotomy _ (Or.inr ⟨_, rfl, hs', hp'⟩)
  have hcard := card_radical_residual_conj (⊤ : Subgroup (adjointGroup .F4 K))
    (Subgroup.mem_top c) x
  rw [top_inf_eq, top_inf_eq] at hcard
  rw [← hcard]
  exact hodd

theorem oddRad_F4_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (x : adjointGroup .F4 K) (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Subgroup.centralizer {x})))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 1) (by omega)
      (by rw [hK, pow_one])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  refine oddRad_F4_two_aux hK (AlgebraicClosure K) (frobenius (AlgebraicClosure K) 2) ?_ x hx
  intro c
  rw [hK]
  exact frobenius_def 2 c

theorem oddRadConcl_F4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (β : MulAut (adjointGroup ReeTag.F4.tag K)) (hβ : orderOf β = 5) :
    OddRadConcl (adjointGroup ReeTag.F4.tag K) β := by
  classical
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 1) (by omega) hK1
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form (f := 1) le_rfl K hK1
  have hβ5 : β ^ 5 = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβ] at this
  have hβinn : β ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range := by
    have hmem : β ∈ Θ.ker := by
      rw [MonoidHom.mem_ker]
      have h5 : Θ β ^ 5 = 1 := by rw [← map_pow, hβ5, map_one]
      have key : ∀ a : Multiplicative (ZMod (2 * 1)), a ^ 5 = 1 → a = 1 := by decide
      exact key _ h5
    rw [hker] at hmem
    exact hmem
  obtain ⟨t, rfl⟩ := hβinn
  have hZ : Subgroup.center (adjointGroup ReeTag.F4.tag K) = ⊥ := center_adjointGroup_eq_bot
  have htord : orderOf t = 5 := by rw [← orderOf_conj_eq hZ t]; exact hβ
  unfold OddRadConcl
  rw [eqLocus_conj_eq_centralizer t]
  exact oddRad_F4_two hK t htord

theorem oddRadAt_smallModel_f4 : OddRadAt (SmallModel .F4) := by
  intro T _ _ _ hS β hβ
  obtain ⟨n, f, hadm, hM, hf⟩ := hS
  have hf1 : f = 1 := hf
  subst hf1
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_F4 hM
  have hK2 : Nat.card K = 2 := by rw [hKcard, pow_one]
  exact oddRadConcl_of_mulEquiv e (fun β' hβ' => oddRadConcl_F4 hK2 β' hβ') β hβ

end CFSG.RankThree.PartOne.F106
