module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.Steinberg.Adjoint.Borel
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.ClassicalInvolution.ModelFacts

section General

variable {U : Type*} [Group U] {D : UniversalRootDatum U}

theorem ggLongRoot_of_symmetric (hirr : IsIrreducible D.cartan)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) (hD : D.divisible = ∅)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : GGLongRoot D γ := by
  have hr : 0 < D.rank := by
    rcases hγ with ⟨w, i, -⟩ | ⟨_, i, -, -⟩ <;> exact Fin.pos i
  obtain ⟨γ₀, hγ₀, hmax⟩ := exists_maxHeight hr
  obtain ⟨c, -, hc⟩ := exists_symmetrizer_eq_smul (hA := D.isFiniteType) hirr
    (d := fun _ => (1 : ℚ)) (fun _ => one_pos) fun i j => by rw [hsym i j]
  have hroots : D.roots = roots D.isFiniteType ∅ := by rw [← hD]
  have hlen : ∀ δ ∈ D.roots, lenSq D.isFiniteType δ = 2 * c := by
    intro δ hδ
    rw [hroots] at hδ
    rcases lenSq_of_mem_roots D.isFiniteType hδ with ⟨i, hi⟩ | ⟨i, hi, -⟩
    · rw [hi, hc, mul_one]
    · exact absurd hi (Set.notMem_empty i)
  obtain ⟨w, hw⟩ := exists_weylAction_eq_of_lenSq_eq D.isFiniteType hirr
    (hroots ▸ hγ₀) (hroots ▸ hγ) (by rw [hlen γ₀ hγ₀, hlen γ hγ])
  exact ⟨w, γ₀, hγ₀, hmax, hw.symm⟩

theorem coprime_two_card_iSup_range_units [Finite U] {k : Type*} [Field k] [Finite k]
    [CharP k 2] {ι : Type*} (φ : ι → kˣ →* U)
    (hc : ∀ i j, ∀ h ∈ (φ i).range, ∀ h' ∈ (φ j).range, Commute h h') :
    Nat.Coprime 2 (Nat.card (⨆ i, (φ i).range : Subgroup U)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨m, -, hm⟩ := FiniteField.card k 2
  have hodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hm]
    have h1 : 1 ≤ 2 ^ (m : ℕ) := Nat.one_le_two_pow
    have h2 : Even (2 ^ (m : ℕ)) := (Nat.even_pow' (PNat.ne_zero m)).2 even_two
    exact Nat.Even.sub_odd h1 h2 odd_one
  refine coprime_two_card_of_sq_eq_one _ fun g hg hg2 => ?_
  have hN : g ^ Nat.card kˣ = 1 := by
    refine CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pow_eq_one_of_mem_iSup
      (fun i h hh => ?_) hc hg
    obtain ⟨t, rfl⟩ := hh
    rw [← map_pow, pow_card_eq_one', map_one]
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  have h2 : orderOf g ∣ Nat.card kˣ := orderOf_dvd_of_pow_eq_one hN
  have h3 : orderOf g ∣ Nat.gcd 2 (Nat.card kˣ) := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left).2 hodd), Nat.dvd_one, orderOf_eq_one_iff]
    at h3
  exact h3

theorem cartanE_symm (r : ℕ) (i j : Fin r) : Tag.cartanE r i j = Tag.cartanE r j i := by
  simp only [Tag.cartanE]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
    congr 1
    apply propext
    omega

theorem mul_comm_of_isParametrization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : CFSG.LieType.Steinberg.RootSystem ι} {K : Type*} [Group K] {X : (ι → ℤ) → Subgroup K}
    {k : Type*} [Field k] {x : (ι → ℤ) → k → K} (hx : IsParametrization (Φ := Φ) X x)
    {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) : ∀ a ∈ X γ, ∀ b ∈ X γ, a * b = b * a := by
  obtain ⟨hmem, hadd, -⟩ := hx γ hγ
  intro a ha b hb
  obtain ⟨c, rfl⟩ := (hmem a).1 ha
  obtain ⟨d, rfl⟩ := (hmem b).1 hb
  rw [← hadd, ← hadd, add_comm]

end General

section Minuscule

open CFSG.LieType.Steinberg.Minuscule

theorem ggRootSylowCentral_e6 {k : Type} [Field k] [Finite k] [CharP k 2] (t : StatedLieTag) :
    GGRootSylowCentral (e6Datum k) t := by
  have : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsym : ∀ i j, (e6Datum k).cartan i j = (e6Datum k).cartan j i := cartanE_symm 6
  exact ggRootSylowCentral_of_longRoot_reduced (e6Datum_isCTGroupDatum k)
    (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k) rfl
    (fun γ _ => isPGroup_two_range_of_charTwo (e6Data_valid.xHom k γ))
    (coprime_two_card_iSup_range_units (fun i => e6Data_valid.hHom k i)
      fun i j h hh h' hh' => (e6Datum_steinbergExtras k).torus_commute i j h hh h' hh')
    (fun γ₀ _ _ => range_mul_comm (e6Data_valid.xHom k γ₀))
    fun γ hγ => ggLongRoot_of_symmetric isIrreducible_E6 hsym rfl hγ.1

theorem ggRootSylowCentral_e7 {k : Type} [Field k] [Finite k] [CharP k 2] (t : StatedLieTag) :
    GGRootSylowCentral (e7Datum k) t := by
  have : Finite (Module.End k (Fin e7Data.d →₀ k)) := Module.finite_of_finite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsym : ∀ i j, (e7Datum k).cartan i j = (e7Datum k).cartan j i := cartanE_symm 7
  exact ggRootSylowCentral_of_longRoot_reduced (e7Datum_isCTGroupDatum k)
    (e7Datum_steinbergExtras k) (e7Datum_bruhatExtras k) rfl
    (fun γ _ => isPGroup_two_range_of_charTwo (e7Data_valid.xHom k γ))
    (coprime_two_card_iSup_range_units (fun i => e7Data_valid.hHom k i)
      fun i j h hh h' hh' => (e7Datum_steinbergExtras k).torus_commute i j h hh h' hh')
    (fun γ₀ _ _ => range_mul_comm (e7Data_valid.xHom k γ₀))
    fun γ hγ => ggLongRoot_of_symmetric isIrreducible_E7 hsym rfl hγ.1

end Minuscule

section Adjoint

open CFSG.LieType.Steinberg.Adjoint

theorem ggRootSylowCentral_e8 {k : Type} [Field k] [Finite k] [CharP k 2] (t : StatedLieTag) :
    GGRootSylowCentral (e8Datum k) t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsym : ∀ i j, (e8Datum k).cartan i j = (e8Datum k).cartan j i := cartanE_symm 8
  exact ggRootSylowCentral_of_longRoot_reduced (e8_isCTGroupDatum k) (e8_steinbergExtras k)
    (e8_bruhatExtras k) rfl
    (fun γ hγ => isPGroup_of_isParametrization (e8_isParametrization k) hγ)
    (coprime_two_card_iSup_range_units (fun i => torusHom (τ := .E8) k i)
      fun i j h hh h' hh' => (e8_steinbergExtras k).torus_commute i j h hh h' hh')
    (fun γ₀ hγ₀ _ => mul_comm_of_isParametrization (e8_isParametrization k) hγ₀)
    fun γ hγ => ggLongRoot_of_symmetric isIrreducible_E8 hsym rfl hγ.1

end Adjoint

end CFSG.StandardType
