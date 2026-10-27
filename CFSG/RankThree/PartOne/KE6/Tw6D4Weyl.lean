module

public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice (e6T3W)
open CFSG.RankThree.Classical (conjSL_sl2Upper conjSL_sl2Lower)
open scoped Matrix MatrixGroups Pointwise

abbrev tw6P (Ω : Type) [Field Ω] :
    ModGL Tag.E6 Ω :=
  diagramMap TwistTag.E6 Ω

@[expose] def tw6WtWord : List (Fin 6) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]

@[expose] def tw6Wt : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word tw6WtWord)

theorem tw6Wt_smul_single (k : Fin Tag.D4.rank) :
    tw6Wt • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (e6Rho (d4Idx k)) 1 := by
  simp only [tw6Wt, wordProd_e6Word_smul]
  revert k
  decide +kernel

theorem tw6Wt_smul_d4Lat (β : Fin Tag.D4.rank → ℤ) :
    tw6Wt • d4Lat β = permLattice e6Rho (d4Lat β) := by
  rw [weyl_smul_d4Lat_eq_sum, d4Lat_eq_sum]
  have h : ∀ k : Fin Tag.D4.rank, tw6Wt • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) =
      permLattice e6Rho (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) := fun k => by
    rw [tw6Wt_smul_single]
    funext j
    simp only [permLattice, Function.comp_apply]
    by_cases hj : j = e6Rho (d4Idx k)
    · subst hj
      simp [Equiv.symm_apply_apply]
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne]
      intro h'
      exact hj (by rw [← h']; simp)
  simp only [h]
  funext j
  simp only [permLattice, Function.comp_apply, Finset.sum_apply, Pi.smul_apply]

@[expose] def d4MaxWord : List (Fin Tag.D4.rank) := [3, 2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 0]

theorem d4Max_smul (x : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem Tag.D4).wordProd d4MaxWord • x = -x := by
  have h : ∀ k : Fin Tag.D4.rank, (coxeterSystem Tag.D4).wordProd d4MaxWord •
      (Pi.single k 1 : Fin Tag.D4.rank → ℤ) = -Pi.single k 1 := fun k => by
    rw [wordProd_smul]
    revert k
    decide +kernel
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin Tag.D4.rank → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [Finset.smul_sum]
  conv_rhs => rw [hx]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm, h k, smul_neg]

theorem tw6_weylType_neg {T W' : WeylGroup Tag.E6} {e : ℕ} (hT : D4TrialityWeylType T e)
    (hW' : ∀ β : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 β → W' • d4Lat β = -(T • d4Lat β)) :
    D4TrialityWeylType W' e := by
  obtain ⟨u, hu⟩ := hT
  refine ⟨(coxeterSystem Tag.D4).wordProd d4MaxWord * u, fun β hβ => ?_⟩
  rw [hW' β hβ, hu β hβ, ← d4Lat_neg, mul_smul, d4Max_smul]


@[expose] def rho4 : Fin Tag.D4.rank → Fin Tag.D4.rank := ![0, 3, 2, 1]

theorem e6Rho_d4Idx (k : Fin Tag.D4.rank) : e6Rho (d4Idx k) = d4Idx (rho4 k) := by
  revert k
  decide

theorem rho4_rho4 (k : Fin Tag.D4.rank) : rho4 (rho4 k) = k := by
  revert k
  decide

theorem exists_monomial_eq_diagramMap_on_d4 {Ω : Type} [Field Ω] [IsAlgClosed Ω] :
    ∃ (m₀ : ModGL Tag.E6 Ω) (hm₀ : m₀ ∈ monomialSubgroup Tag.E6 Ω),
      weylQuotientHom Tag.E6 Ω ⟨m₀, hm₀⟩ = tw6Wt ∧
      ∀ y ∈ subsystemGroup Tag.E6 Ω d4Support,
        m₀ * y * m₀⁻¹ = tw6P Ω * y * (tw6P Ω)⁻¹ := by
  classical
  set n := canonicalRep (coxeterSystem Tag.E6) Ω tw6Wt with hn
  have hnM : n ∈ monomialSubgroup Tag.E6 Ω := canonicalRep_mem_monomialSubgroup Ω tw6Wt
  have hW : weylQuotientHom Tag.E6 Ω ⟨n, hnM⟩ = tw6Wt :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep tw6Wt)
  have hsc : ∀ k : Fin Tag.D4.rank, ∃ s : Ωˣ, ∀ c : Ω,
      n * xUnit Tag.E6 Ω (d4Idx k) c * n⁻¹ = xUnit Tag.E6 Ω (d4Idx (rho4 k)) (s * c) ∧
      n * yUnit Tag.E6 Ω (d4Idx k) c * n⁻¹ =
        yUnit Tag.E6 Ω (d4Idx (rho4 k)) (((s⁻¹ : Ωˣ) : Ω) * c) := by
    intro k
    obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq hnM (mapsRootLines_weylQuotientHom ⟨n, hnM⟩)
      (isRoot_single Tag.E6 (d4Idx k))
      (show weylQuotientHom Tag.E6 Ω ⟨n, hnM⟩ •
          (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (d4Idx (rho4 k)) 1 by
        rw [hW, tw6Wt_smul_single, e6Rho_d4Idx])
    refine ⟨s, fun c => ⟨?_, ?_⟩⟩
    · have h := hs (uSL c)
      rw [rootSL2_single_apply, rootSL2_single_apply, simpleRootSL2_uSL] at h
      rw [h]
      exact (congrArg (simpleRootSL2 Tag.E6 Ω (d4Idx (rho4 k))) (conjSL_sl2Upper s c)).trans
        (simpleRootSL2_uSL _ _)
    · have h := hs (vSL c)
      rw [rootSL2_single_apply, rootSL2_single_apply, simpleRootSL2_vSL] at h
      rw [h]
      exact (congrArg (simpleRootSL2 Tag.E6 Ω (d4Idx (rho4 k))) (conjSL_sl2Lower s c)).trans
        (simpleRootSL2_vSL _ _)
  choose s hs using hsc
  obtain ⟨t, ht⟩ := exists_d4TorusHom_scalars (Ω := Ω) (fun k' => (s (rho4 k'))⁻¹)
  set d := d4TorusHom Ω t with hd
  have hdT : d ∈ torusGroup Tag.E6 Ω := d4TorusHom_mem_torusGroup t
  have hdM : d ∈ monomialSubgroup Tag.E6 Ω := torusGroup_le_monomialSubgroup hdT
  refine ⟨d * n, mul_mem hdM hnM, ?_, ?_⟩
  · have e : (⟨d * n, mul_mem hdM hnM⟩ : monomialSubgroup Tag.E6 Ω) = ⟨d, hdM⟩ * ⟨n, hnM⟩ := rfl
    rw [e, map_mul, hW, weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hdT), one_mul]
  · intro y hy
    have hext : (MulAut.conj (d * n)).toMonoidHom.comp
        (subsystemGroup Tag.E6 Ω d4Support).subtype =
        (MulAut.conj (tw6P Ω)).toMonoidHom.comp
          (subsystemGroup Tag.E6 Ω d4Support).subtype := by
      refine d4Q_hom_ext (fun k c => ?_) (fun k c => ?_)
      · simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        have h1 : d * n * xUnit Tag.E6 Ω (d4Idx k) c * (d * n)⁻¹ =
            d * (n * xUnit Tag.E6 Ω (d4Idx k) c * n⁻¹) * d⁻¹ := by group
        rw [h1, (hs k c).1, (ht (rho4 k) _).1, rho4_rho4]
        have h2 : tw6P Ω * xUnit Tag.E6 Ω (d4Idx k) c * (tw6P Ω)⁻¹ =
            xUnit Tag.E6 Ω (e6Rho (d4Idx k)) c :=
          diagramMap_mul_xUnit_mul_inv TwistTag.E6 Ω (d4Idx k) c
        rw [h2, e6Rho_d4Idx, Units.inv_mul_cancel_left]
      · simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        have h1 : d * n * yUnit Tag.E6 Ω (d4Idx k) c * (d * n)⁻¹ =
            d * (n * yUnit Tag.E6 Ω (d4Idx k) c * n⁻¹) * d⁻¹ := by group
        rw [h1, (hs k c).2, (ht (rho4 k) _).2, rho4_rho4]
        have h2 : tw6P Ω * yUnit Tag.E6 Ω (d4Idx k) c * (tw6P Ω)⁻¹ =
            yUnit Tag.E6 Ω (e6Rho (d4Idx k)) c :=
          diagramMap_mul_yUnit_mul_inv TwistTag.E6 Ω (d4Idx k) c
        rw [h2, e6Rho_d4Idx, inv_inv, Units.mul_inv_cancel_left]
    have h := DFunLike.congr_fun hext ⟨y, hy⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] at h
    exact h

end CFSG.RankThree.PartOne.KE6
