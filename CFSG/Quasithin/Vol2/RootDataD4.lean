module

public import CFSG.Quasithin.H13.NQCatD4Center
public import CFSG.Quasithin.H13.NQCatD4Irred
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.H13.RootData.D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4 CFSG.Quasithin.H13.NQCat
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped Pointwise

theorem isRoot_rho : IsRoot TwistTag.D4.tag (trialityRoot 5) := by
  rw [← mem_rootFinset]
  decide +kernel

theorem not_isRoot_add_rho {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (hβ0 : 0 < height β) :
    ¬ IsRoot TwistTag.D4.tag (β + trialityRoot 5) := by
  have h : ∀ β ∈ (rootFinset TwistTag.D4.tag).filter (fun β => 0 < height β),
      β + trialityRoot 5 ∉ rootFinset TwistTag.D4.tag := by
    decide +kernel
  have hmem : β ∈ (rootFinset TwistTag.D4.tag).filter (fun β => 0 < height β) :=
    Finset.mem_filter.2 ⟨mem_rootFinset.2 hβ, hβ0⟩
  intro hr
  exact h β hmem (mem_rootFinset.2 hr)

theorem commute_highestRoot
    {K : Type} [Field K] (c : K) {y : ModGL TwistTag.D4.tag K}
    (hy : y ∈ posUnipotent TwistTag.D4.tag K) :
    y * pinnedX TwistTag.D4.tag K (trialityRoot 5) c =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) c * y := by
  have hle : posUnipotent TwistTag.D4.tag K ≤ Subgroup.centralizer
      {pinnedX TwistTag.D4.tag K (trialityRoot 5) c} := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    by_cases hβρ : β = trialityRoot 5
    · subst hβρ
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · have hne' : β ≠ -trialityRoot 5 := by
        intro h
        have h1 := hβ.2
        rw [h] at h1
        revert h1
        decide
      have hc : Commute (pinnedX TwistTag.D4.tag K β d)
          (pinnedX TwistTag.D4.tag K (trialityRoot 5) c) :=
        (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) hβ.1 isRoot_rho
          hβρ hne').2 (not_isRoot_add_rho hβ.1 hβ.2) K _ (mem_rootSubgroup.2 ⟨d, rfl⟩) _
          (mem_rootSubgroup.2 ⟨c, rfl⟩)
      exact hc.eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem torus_conj_highestRoot
    {K : Type} [Field K] {t : ModGL TwistTag.D4.tag K} (ht : t ∈ torusGroup TwistTag.D4.tag K) :
    ∃ l : Kˣ, ∀ s : K, t * pinnedX TwistTag.D4.tag K (trialityRoot 5) s * t⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) ((l : K) * s) := by
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, u⟩, rfl⟩ := hx
    exact ⟨u ^ (∑ j, TwistTag.D4.tag.cartan i j * trialityRoot 5 j),
      fun s => root_torus_conjugation i isRoot_rho u s⟩
  | one => exact ⟨1, fun s => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, fun s => ?_⟩
    calc x * y * pinnedX TwistTag.D4.tag K (trialityRoot 5) s * (x * y)⁻¹ =
        x * (y * pinnedX TwistTag.D4.tag K (trialityRoot 5) s * y⁻¹) * x⁻¹ := by group
      _ = pinnedX TwistTag.D4.tag K (trialityRoot 5) ((a * b : Kˣ) * s) := by
        rw [hb, ha, Units.val_mul, mul_assoc]
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨a⁻¹, fun s => ?_⟩
    have h := ha (((a⁻¹ : Kˣ) : K) * s)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h
    calc x⁻¹ * pinnedX TwistTag.D4.tag K (trialityRoot 5) s * x⁻¹⁻¹ =
        x⁻¹ * (x * pinnedX TwistTag.D4.tag K (trialityRoot 5) (((a⁻¹ : Kˣ) : K) * s) * x⁻¹) *
          x := by
          rw [h, inv_inv]
      _ = pinnedX TwistTag.D4.tag K (trialityRoot 5) (((a⁻¹ : Kˣ) : K) * s) := by group

theorem exists_torus_mul_eq_of_mem_graphFixedRootBorel
    {K : Type} [Field K] (σ : K →+* K) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedRootBorel TwistTag.D4 K σ) :
    ∃ t ∈ torusGroup TwistTag.D4.tag K, ∃ u ∈ posUnipotent TwistTag.D4.tag K, t * u = g := by
  have hgB : g ∈ (SetLike.coe (torusGroup TwistTag.D4.tag K) *
      SetLike.coe (posUnipotent TwistTag.D4.tag K) : Set (ModGL TwistTag.D4.tag K)) := by
    rw [← (triangular_borel_structure.{0, 0} TwistTag.D4.tag K).2.2.2.2.1]
    exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).1
  obtain ⟨t, ht, u, hu, htu⟩ := Set.mem_mul.mp hgB
  exact ⟨t, ht, u, hu, htu⟩

theorem exists_eq_ox₆_of_centralizer
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    {g : ModGL TwistTag.D4.tag K} (hgC : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hcU : ∀ y ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, y * g = g * y) :
    ∃ d : trialityFixedField K σ.toRingHom, g = ox₆ σ d := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨-, -, -, -, -, -, hNU, -⟩ := fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀
  have hgN : g ∈ Subgroup.normalizer
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [show g * h * g⁻¹ = h by rw [← hcU h hh]; group]
      exact hh
    · intro hh
      have h1 := hcU _ hh
      have e : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [h1]
          _ = g * h * g⁻¹ := by group
      rw [e]
      exact hh
  have hgB : g ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    rw [← hNU]
    exact ⟨hgC, hgN⟩
  obtain ⟨-, -, -, hsc⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  have hgP : g ∈ P0 σ := graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hgB
  have hQU : Q0 σ ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedPosUnipotent _
  have hgCQ : g ∈ Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcU y (hQU hy)
  exact D4Center.eq_ox₆_of_mem_center_a0 σ hσ3 ⟨hsc ⟨hgP, hgCQ⟩, hgCQ⟩

theorem eq_one_of_centralizer_of_odd
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    {g : ModGL TwistTag.D4.tag K} (hgC : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hcU : ∀ y ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, y * g = g * y)
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨d, rfl⟩ := exists_eq_ox₆_of_centralizer σ hσ3 hgC hcU
  have hdd : d + d = 0 := Subtype.ext (by
    rw [Subfield.coe_add, CharTwo.add_self_eq_zero]
    rfl)
  have h2 : ox₆ σ d ^ 2 = 1 := by rw [sq, ← ox₆_add σ hσ3, hdd, ox₆_zero σ hσ3]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  have h1 : orderOf (ox₆ σ d) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem graphFixedPosUnipotent_le_perfectCore_one
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom))
    (hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom fa1), s.card = 4) :
    graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ perfectCore (P1 σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hU2 := isPGroup_posUnipotent σ hσ3
  obtain ⟨R, hRx, -, -, hRP, -, -⟩ := levi_package σ fa1 hU2 hL4
  obtain ⟨hQP, -, -, -⟩ := library_facts σ fa1 singleton_ne_univ_fa1
  have hQ1 : Q1 σ ≤ perfectCore (P1 σ) := by
    refine (generation_a1 σ hσ3 hU2 hk4).trans (Subgroup.commutator_le.2 fun q hq x hx => ?_)
    have hqN : q ∈ Subgroup.normalizer (perfectCore (P1 σ) : Set (ModGL TwistTag.D4.tag K)) :=
      CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer (hQP hq))
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hqN x).1 hx) (inv_mem hx)
  have hV : graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom fa1 = Q1 σ :=
    (radical_eq_simpleComplement σ.toRingHom fa1 supp_fa1).symm
  obtain ⟨-, -, hmul, -⟩ := fixed_simple_positive_complement TwistTag.D4 K σ fa1
  intro u hu
  have hu' : u ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K)) := hu
  rw [hmul] at hu'
  obtain ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩ := hu'
  refine mul_mem (hQ1 (hV ▸ hv)) ?_
  show (orbitX TwistTag.D4 K σ.toRingHom fa1 c : ModGL TwistTag.D4.tag K) ∈ perfectCore (P1 σ)
  rw [← hRx c]
  exact hRP ⟨_, rfl⟩

end CFSG.Quasithin.H13.RootData.D4
