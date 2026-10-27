module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Fixed
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

theorem prod_zpow_sum_E6 {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι) (ζ : G)
    (z : ι → ℤ) : ∏ i ∈ s, ζ ^ z i = ζ ^ ∑ i ∈ s, z i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

theorem sum_mul_eq_zero_of_mem_E6 {k : Type*} [Field k] {m n : ℕ} {V : Submodule k (Fin m → k)}
    (B : Module.Basis (Fin n) k V) {e : Fin m → k}
    (he : ∀ j, ∑ i, (B j : Fin m → k) i * e i = 0) {v : Fin m → k} (hv : v ∈ V) :
    ∑ i, v i * e i = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin n → k, v = ∑ j, c j • (B j : Fin m → k) := by
    refine ⟨B.repr ⟨v, hv⟩, ?_⟩
    have h := congrArg (fun x : V => (x : Fin m → k)) (B.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  rw [hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, he j, mul_zero]

theorem exists_annihilator_E6 {k : Type*} [Field k] [Finite k] {m d : ℕ}
    (V : Submodule k (Fin m → k)) (hV : Module.finrank k V ≤ d) :
    ∃ E : Set (Fin m → k), Nat.card k ^ (m - d) ≤ E.ncard ∧
      ∀ e ∈ E, ∀ v ∈ V, ∑ i, v i * e i = 0 := by
  let B := Module.finBasis k V
  let L : (Fin m → k) →ₗ[k] (Fin (Module.finrank k V) → k) :=
    Matrix.mulVecLin (Matrix.of fun j i => ((B j : V) : Fin m → k) i)
  refine ⟨(LinearMap.ker L : Set (Fin m → k)), ?_, fun e he v hv => ?_⟩
  · have h := LinearMap.finrank_range_add_finrank_ker L
    have h1 : Module.finrank k (LinearMap.range L) ≤ Module.finrank k V := by
      simpa using Submodule.finrank_le (LinearMap.range L)
    simp only [Module.finrank_fin_fun] at h
    have h2 : m - d ≤ Module.finrank k (LinearMap.ker L) := by omega
    rw [← Nat.card_coe_set_eq]
    change _ ≤ Nat.card (LinearMap.ker L)
    rw [Module.natCard_eq_pow_finrank (K := k) (V := LinearMap.ker L)]
    exact Nat.pow_le_pow_right (Nat.card_pos (α := k)) h2
  · have hLe : L e = 0 := LinearMap.mem_ker.1 he
    exact sum_mul_eq_zero_of_mem_E6 B (fun j => by
      simpa [L, Matrix.mulVec, dotProduct] using congrFun hLe j) hv

theorem false_of_ncard_le_of_fix_wRho_E6 {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ) {F : Set (Fin Tag.E6.rank → Kˣ)}
    {w : WeylGroup Tag.E6}
    (hθ : ∀ β, w • permLattice (exactPerm .E6 1) (w • permLattice (exactPerm .E6 1) β) = β)
    (hfix : ∀ β ∈ famKernel F, w • permLattice (exactPerm .E6 1) β = β)
    (hrank : Set.ncard {b : Fin Tag.E6.rank → Kˣ | (∀ i, b i ^ p = 1) ∧
      ∀ β ∈ famKernel F, rootChar b β = 1} ≤ p) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpK
  have hzp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨E, hEcard, hE⟩ := exists_annihilator_E6 (k := ZMod p) _
    (fixed_span_finrank_le_four_E6 (K := ZMod p) (ε := 1) rfl hθ hfix)
  rw [Nat.card_zmod] at hEcard
  let φ : (Fin Tag.E6.rank → ZMod p) → (Fin Tag.E6.rank → Kˣ) := fun e i => ζ ^ (e i).val
  have hφinj : Function.Injective φ := by
    intro e e' h
    funext i
    have h1 := (pow_inj_mod).1 (congrFun h i)
    rw [hζ, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h1
    exact ZMod.val_injective p h1
  have hsub : φ '' E ⊆
      {b : Fin Tag.E6.rank → Kˣ | (∀ i, b i ^ p = 1) ∧ ∀ β ∈ famKernel F, rootChar b β = 1} := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨fun i => ?_, fun β hβ => ?_⟩
    · simp only [φ]
      rw [← pow_mul, mul_comm, pow_mul, hzp, one_pow]
    · have hdot := hE e he _ (Submodule.subset_span ⟨β, hβ, rfl⟩)
      have hrc : rootChar (φ e) β = ζ ^ ∑ i, ((e i).val : ℤ) * β i := by
        simp only [rootChar, φ]
        rw [← prod_zpow_sum_E6]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← zpow_natCast, ← zpow_mul]
      rw [hrc, ← orderOf_dvd_iff_zpow_eq_one, hζ, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      rw [← hdot]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ hφinj] at h3
  have h4 : p ^ 2 ≤ p := hEcard.trans (h3.trans hrank)
  nlinarith [hp.two_le]

end KGCentE6

end CFSG.StandardType
