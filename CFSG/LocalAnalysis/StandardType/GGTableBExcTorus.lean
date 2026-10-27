module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExc

variable {τ : Tag} {K : Type} [Field K]

theorem exists_rootGroup_normalized [CharP K 2] {p : ℕ} [NeZero p] (i₀ : Fin τ.rank) (ζ : Kˣ)
    (hζ : ζ ^ p = 1) :
    ∃ U : Subgroup (adjointGroup τ K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ v, ∀ u ∈ U, chevTorus τ ζ hζ v * u * (chevTorus τ ζ hζ v)⁻¹ ∈ U := by
  classical
  let xh : Multiplicative K →* adjointGroup τ K :=
    { toFun := fun c => ⟨xUnit τ K i₀ (Multiplicative.toAdd c), xUnit_mem_adjointGroup _ _⟩
      map_one' := Subtype.ext (xUnit_zero i₀)
      map_mul' := fun c c' => Subtype.ext (xUnit_add i₀ _ _) }
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨xh.range, fun h => ?_, ?_, ?_⟩
  · have h1 : xh (.ofAdd 1) ∈ xh.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : xOp τ K i₀ 1 = xOp τ K i₀ 0 := by
      have h3 : xUnit τ K i₀ 1 = xUnit τ K i₀ 0 := by
        rw [xUnit_zero]
        exact congrArg Subtype.val h1
      exact congrArg Units.val h3
    exact one_ne_zero (xOp_injective i₀ h2)
  · rintro ⟨_, ⟨c, rfl⟩⟩
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    change (xUnit τ K i₀ (Multiplicative.toAdd c)) ^ 2 = 1
    rw [pow_two, ← xUnit_add, ← two_mul, htwo, zero_mul, xUnit_zero]
  · rintro a _ ⟨c, rfl⟩
    obtain ⟨c', hc'⟩ := listProd_torusElt_conj_xUnit i₀
      (List.ofFn fun i => torusElt τ K i (zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd a i))))
      (fun g hg => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
        exact ⟨i, _, rfl⟩) (Multiplicative.toAdd c)
    refine ⟨.ofAdd c', Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_chevTorus]
    exact hc'.symm

theorem ggTorusLift_adjoint [Finite K] [CharP K 2] (hr : 0 < τ.rank) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p)) :
    GGTorusLift p τ.rank (adjointGroup τ K) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨U, hU, hU2, hTU⟩ := exists_rootGroup_normalized ⟨0, hr⟩ ζ hζ
  exact TableBF4.ggTorusLift_of_reflections (d := τ.rank) hp hp2 (chevTorus τ ζ hζ)
    (chevTorus_injective hζo hζ hdet) (cartanFunctional τ p)
    (fun i => CFSG.RankThree.CentralCover.cartanFunctional_single i)
    (fun i => ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩)
    (fun i v => weylElt_conj_chevTorus ζ hζ i v) hU hU2 hTU

theorem isUnit_det_cartan_of_eq {p : ℕ} (hp : p.Prime) {d : ℕ} (hdet : τ.cartan.det = d)
    (hd : Nat.Coprime d p) : IsUnit ((τ.cartan.det : ℤ) : ZMod p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [hdet]
  exact isUnit_natCast_of_coprime hd


theorem ggTorusLift_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : GGTorusLift p 8 (RecipeGroup .E8 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (recipeEquiv .E8 K)
    (ggTorusLift_adjoint (τ := .E8) (by decide) hp hp2 hpq
      (isUnit_det_cartan_of_eq hp det_cartan_E8 (Nat.coprime_one_left p)))

theorem ggTorusLift_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : GGTorusLift p 7 (RecipeGroup .E7 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (recipeEquiv .E7 K)
    (ggTorusLift_adjoint (τ := .E7) (by decide) hp hp2 hpq
      (isUnit_det_cartan_of_eq hp det_cartan_E7
        ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))))

theorem ggTorusLift_E6 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) : GGTorusLift p 6 (RecipeGroup .E6 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (recipeEquiv .E6 K)
    (ggTorusLift_adjoint (τ := .E6) (by decide) hp hp2 hpq
      (isUnit_det_cartan_of_eq hp det_cartan_E6
        ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))))

end TableBExc

end CFSG.StandardType
