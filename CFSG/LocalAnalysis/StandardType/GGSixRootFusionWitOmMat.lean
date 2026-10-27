module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmInv
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

namespace WitOm

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions TableBOrth CFSG.Assembly
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply statedOmega_eq_comap)
open scoped Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem polar_mulVec_of_mem {QF : QuadraticForm K (ι → K)} {M : GL ι K}
    (hM : M ∈ LargeEvenOrthGroup ⇑QF) (u v : ι → K) :
    polar QF ((M : Matrix ι ι K) *ᵥ u) ((M : Matrix ι ι K) *ᵥ v) = polar QF u v := by
  have h := isometry_of_mem_orthGroup hM
  rw [polar, polar, ← Matrix.mulVec_add, h, h, h]

omit [Fintype ι] in
theorem apply_eq_zero_of_mem_span {a : Fin 2 → ι} {x : ι → K}
    (hx : x ∈ Submodule.span K (Set.range fun j => (Pi.single (a j) 1 : ι → K))) {y : ι}
    (hy : ∀ j, y ≠ a j) : x y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun j _ => by
    rw [Pi.smul_apply, Pi.single_eq_of_ne (hy j), smul_zero]

theorem commute_diagGL_of_stable {QF : QuadraticForm K (ι → K)} {M : GL ι K}
    (hMO : M ∈ LargeEvenOrthGroup ⇑QF) (hMM : M * M = 1) {a b : Fin 2 → ι}
    (hab : ∀ k, SeitzReduction.OmegaPilot.IsHypCoord QF (a k) (b k))
    (hE : ∀ i, (M : Matrix ι ι K) *ᵥ Pi.single (a i) 1 ∈
      Submodule.span K (Set.range fun j => (Pi.single (a j) 1 : ι → K)))
    (hF : ∀ i, (M : Matrix ι ι K) *ᵥ Pi.single (b i) 1 ∈
      Submodule.span K (Set.range fun j => (Pi.single (b j) 1 : ι → K)))
    {δ : ι → Kˣ} (hδa : ∀ i, δ (a i) = δ (a 0)) (hδb : ∀ i, δ (b i) = δ (b 0))
    (hδ : ∀ x, (∀ i, x ≠ a i ∧ x ≠ b i) → δ x = 1) :
    M * TauCeti.diagGL δ = TauCeti.diagGL δ * M := by
  rw [commute_diagGL_iff]
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hcol : (M : Matrix ι ι K) x y = ((M : Matrix ι ι K) *ᵥ Pi.single y 1) x := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hMM' : ∀ u, (M : Matrix ι ι K) *ᵥ ((M : Matrix ι ι K) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hMM, Units.val_one, Matrix.one_mulVec]
  by_cases hya : ∃ i, y = a i
  · obtain ⟨i, rfl⟩ := hya
    by_cases hxa : ∃ j, x = a j
    · obtain ⟨j, rfl⟩ := hxa
      rw [hδa i, hδa j, mul_comm]
    · push Not at hxa
      rw [hcol, apply_eq_zero_of_mem_span (hE i) hxa, zero_mul, mul_zero]
  by_cases hyb : ∃ i, y = b i
  · obtain ⟨i, rfl⟩ := hyb
    by_cases hxb : ∃ j, x = b j
    · obtain ⟨j, rfl⟩ := hxb
      rw [hδb i, hδb j, mul_comm]
    · push Not at hxb
      rw [hcol, apply_eq_zero_of_mem_span (hF i) hxb, zero_mul, mul_zero]
  push Not at hya hyb
  rw [hδ y fun i => ⟨hya i, hyb i⟩, Units.val_one, mul_one]
  by_cases hx : ∀ i, x ≠ a i ∧ x ≠ b i
  · rw [hδ x hx, Units.val_one, one_mul]
  push Not at hx
  obtain ⟨j, hj⟩ := hx
  have hzero : (M : Matrix ι ι K) x y = 0 := by
    rw [hcol]
    by_cases hxa : x = a j
    ·
      rw [hxa, ← (hab j).polar_right ((M : Matrix ι ι K) *ᵥ Pi.single y 1),
        ← hMM' (Pi.single (b j) 1), polar_mulVec_of_mem hMO]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hF j)
      rw [← hc, ← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, (hab k).polar_right,
          Pi.single_eq_of_ne (hya k).symm, smul_zero]
    · rw [hj hxa, ← (hab j).polar_left ((M : Matrix ι ι K) *ᵥ Pi.single y 1),
        ← hMM' (Pi.single (a j) 1), polar_mulVec_of_mem hMO]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hE j)
      rw [← hc, ← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, (hab k).polar_left,
          Pi.single_eq_of_ne (hyb k).symm, smul_zero]
  rw [hzero, mul_zero]

theorem exists_omega_conj_stable [Finite K] [CharP K 2] {QF : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin QF).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, QF x = 0)
    {a b : Fin 2 → ι} (hab : ∀ k, SeitzReduction.OmegaPilot.IsHypCoord QF (a k) (b k))
    (hb : Function.Injective b) (hab' : ∀ i j, a i ≠ b j) {w : ι → K} (hw : QF w ≠ 0)
    (hwb : ∀ i, w (b i) = 0) (hwa : ∀ i, w (a i) = 0)
    {v : GL ι K} (hvO : v ∈ LargeEvenOrthGroup ⇑QF) (hvv : v * v = 1) (hv1 : v ≠ 1) :
    ∃ h ∈ LargeEvenOmega ⇑QF,
      (∀ i, ((h⁻¹ * v * h : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (a i) 1 ∈
        Submodule.span K (Set.range fun j => (Pi.single (a j) 1 : ι → K))) ∧
      ∀ i, ((h⁻¹ * v * h : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (b i) 1 ∈
        Submodule.span K (Set.range fun j => (Pi.single (b j) 1 : ι → K)) := by
  set t := toLinEquiv ι K v with ht
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup QF := mem_orthGroup_iff_toLinEquiv.mp hvO
  have htt : t * t = 1 := by rw [ht, ← map_mul, hvv, map_one]
  have ht1 : t ≠ 1 := fun h => hv1 ((toLinEquiv ι K).injective (by rw [← ht, h, map_one]))
  have hdim : finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  obtain ⟨e, f, hef, hte, htf⟩ := exists_hypFamily_stable hnd htO htt ht1 (by omega)
  have he₀ : IsHypFamily QF (fun k => Pi.single (a k) 1) (fun k => Pi.single (b k) 1) :=
    isHypFamily_single hab hb hab'
  obtain ⟨g, hg, hge⟩ := exists_orthDerived_apply_eq hnd hT he₀ hef hw
    (fun i => by rw [polar_comm, (hab i).polar_left, hwb i])
    (fun i => by rw [polar_comm, (hab i).polar_right, hwa i])
  set h := (toLinEquiv ι K).symm g with hh
  have hhΩ : h ∈ LargeEvenOmega ⇑QF := by
    have h1 : h ∈ CFSG.Assembly.LowTwoRank.StatedOmega ⇑QF := by
      rw [statedOmega_eq_comap rfl, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hh,
        MulEquiv.apply_symm_apply]
      exact hg
    exact h1
  have hginv : ∀ j, g⁻¹ (e j) = Pi.single (a j) 1 ∧ g⁻¹ (f j) = Pi.single (b j) 1 := fun j => by
    constructor
    · rw [← (hge j).1, ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]
    · rw [← (hge j).2, ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]
  have hmap : ∀ x, ((h⁻¹ * v * h : GL ι K) : Matrix ι ι K) *ᵥ x = g⁻¹ (t (g x)) := fun x => by
    rw [← toLinEquiv_apply, map_mul, map_mul, map_inv, hh, MulEquiv.apply_symm_apply, ← ht]
    rfl
  refine ⟨h, hhΩ, fun i => ?_, fun i => ?_⟩
  · rw [hmap, (hge i).1]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hte i)
    rw [← hc, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, (hginv j).1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [hmap, (hge i).2]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (htf i)
    rw [← hc, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, (hginv j).2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end WitOm

end CFSG.StandardType
