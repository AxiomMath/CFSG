module

public import CFSG.RankThree.SteinbergR3ECALinearNonsplitPlaneCores
public import CFSG.RankThree.PartOne.KC.LinearInnerPlaneProductsTrivial

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module Matrix Subgroup CFSG CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary

section Bridge

variable {n : ℕ} {K : Type} [Field K]

theorem commutantEquivPi_eq_one_of_matrix_eq_one {x : Module.End K (Fin n → K)}
    (hx : Squarefree (minpoly K x)) (r : commutant x) (a : primaryFactors x)
    (h : commutantEquivMatrix hx r a = 1) : commutantEquivPi hx r a = 1 :=
  (LinearMap.toMatrixAlgEquiv (Module.finBasis (AdjoinRoot (a : K[X]))
    (primaryComponent x (a : K[X])))).injective (h.trans (map_one _).symm)

theorem toLin_mem_linearSpecialBlock_of_mem_blockImage
    (x : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hx : Squarefree (minpoly K (x : Module.End K (Fin n → K))))
    (h : primaryFactors (x : Module.End K (Fin n → K))) {g : GL (Fin n) K}
    (hg : g ∈ blockImage hx h) :
    Matrix.GeneralLinearGroup.toLin g ∈ linearSpecialBlock x (h : K[X]) := by
  classical
  obtain ⟨s, rfl⟩ := mem_blockImage.mp hg
  set w : PiGL (Efac (x : Module.End K (Fin n → K))) (mult (x : Module.End K (Fin n → K))) :=
    blockEmbed (Efac (x : Module.End K (Fin n → K))) (mult (x : Module.End K (Fin n → K))) h s
    with hw
  set u : (commutant (x : Module.End K (Fin n → K)))ˣ := thetaEquivUnits hx w with hu
  have hmat := commutantEquivMatrix_thetaEquivUnits hx w
  have hlin : ((Matrix.GeneralLinearGroup.toLin (blockTheta hx w) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) =
      ((u : commutant (x : Module.End K (Fin n → K))) : Module.End K (Fin n → K)) := by
    change Matrix.toLin' ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
      Module.End K (Fin n → K)).symm
        ((u : commutant (x : Module.End K (Fin n → K))) : Module.End K (Fin n → K))) = _
    rw [← toLinAlgEquiv'_eq_toLin']
    exact AlgEquiv.apply_symm_apply _ _
  have hcent : Matrix.GeneralLinearGroup.toLin (blockTheta hx w) ∈ gl_centralizer x := by
    rw [mem_gl_centralizer, hlin]
    exact (mem_commutant _).mp (u : commutant (x : Module.End K (Fin n → K))).2
  refine ⟨hcent, fun j hj hjh v hv => ?_, ?_⟩
  ·
    have hne : (⟨j, hj⟩ : primaryFactors (x : Module.End K (Fin n → K))) ≠ h :=
      fun e => hjh (congrArg Subtype.val e)
    have h1 := congrFun hmat ⟨j, hj⟩
    rw [hw, blockEmbed_apply_of_ne hne, Units.val_one] at h1
    have h3 := commutantEquivPi_eq_one_of_matrix_eq_one hx
      (u : commutant (x : Module.End K (Fin n → K))) ⟨j, hj⟩ h1
    rw [hlin]
    have h4 := congrArg (fun T => ((T ⟨v, hv⟩ : primaryComponent
      (x : Module.End K (Fin n → K)) j) : Fin n → K)) h3
    exact h4
  ·
    have hres : (⟨((Matrix.GeneralLinearGroup.toLin (blockTheta hx w) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)),
        mem_commutant_of_mem_gl_centralizer hcent⟩ : commutant (x : Module.End K (Fin n → K))) =
        (u : commutant (x : Module.End K (Fin n → K))) := Subtype.ext hlin
    rw [hres]
    have h1 := congrFun hmat h
    rw [hw, blockEmbed_apply_self] at h1
    have h2 : LinearMap.toMatrix (Module.finBasis (AdjoinRoot (h : K[X]))
        (primaryComponent (x : Module.End K (Fin n → K)) h))
        (Module.finBasis (AdjoinRoot (h : K[X]))
        (primaryComponent (x : Module.End K (Fin n → K)) h))
        (commutantRestrict (h : K[X]) (u : commutant (x : Module.End K (Fin n → K)))) =
        (s : Matrix (Fin (mult (x : Module.End K (Fin n → K)) h))
          (Fin (mult (x : Module.End K (Fin n → K)) h)) (Efac (x : Module.End K (Fin n → K)) h)) :=
      h1
    rw [← LinearMap.det_toMatrix (Module.finBasis (AdjoinRoot (h : K[X]))
      (primaryComponent (x : Module.End K (Fin n → K)) h)), h2]
    exact s.2

end Bridge

theorem linear_nonsplit_all_dimension_inner_plane_local_core_centralization_of_CA :
    LinearNonsplitAllDimensionInnerPlaneLocalCoreCentralization := by
  intro p ℓ f n K _ hp hp3 hℓ hℓp hf hn3 hK hpq B hB E hE hEel hEcard
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have := hEel
  obtain ⟨⟨E₀, ⟨hE₀el, hE₀card, hE₀map, hE₀inj⟩, -⟩, hmain⟩ :=
    linear_nonsplit_all_dimension_inner_plane_local_core_centralization hp hp3 hℓ hℓp hf hn3 hK
      hpq B hB E hE hEcard
  refine ⟨E₀, hE₀el, hE₀card, hE₀map, hE₀inj, ?_, ?_⟩
  · intro a haE₀ ha1 hsq h hgood s hs g hg
    obtain ⟨-, -, -, -, hgoodcase⟩ := (hmain E₀ hE₀el hE₀map a haE₀ ha1).1 h.1 h.2
    have hgood' : 3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K))
          : Module.End K (Fin n → K)) h.1 ∨
        (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) h.1 = 2 ∧ 3 < Nat.card (AdjoinRoot h.1)) := by
      rcases hgood with h3 | ⟨h2, hc⟩
      · exact Or.inl h3
      · by_cases h3 : 3 ≤ primaryMultiplicity ((slGL n K a :
            LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) h.1
        · exact Or.inl h3
        · have h2' : 2 ≤ primaryMultiplicity ((slGL n K a :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) h.1 := h2
          exact Or.inr ⟨by omega, hc⟩
    have hL := toLin_mem_linearSpecialBlock_of_mem_blockImage (slGL n K a) hsq h hg
    obtain ⟨s', hs'⟩ := linearSpecialBlock_le_range_slGL hsq h.2 hL
    have hg' : g = SpecialLinearGroup.toGL s' :=
      Matrix.GeneralLinearGroup.toLin.injective hs'.symm
    have hmem : conjAut n K g ∈ ((linearSpecialBlock (slGL n K a) h.1).comap (slGL n K)).map
        (innerOfSL n K) := by
      refine Subgroup.mem_map.mpr ⟨s', ?_, ?_⟩
      · rw [Subgroup.mem_comap, hs']
        exact hL
      · show MulAut.conj (proj n K s') = conjAut n K g
        rw [hg', conjAut_toGL]
    exact (hgoodcase hgood').2.2.2.2 s hs _ hmem
  · intro t htE ht1
    rw [← hE₀map] at htE
    obtain ⟨a, haE₀, rfl⟩ := Subgroup.mem_map.mp htE
    have ha1 : a ≠ 1 := fun h1 => ht1 (by rw [h1, map_one])
    have hcomm := (hmain E₀ hE₀el hE₀map a haE₀ ha1).2.2.2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hcomm s hs e he).symm

theorem linear_nonsplit_inner_plane_products_trivial : LinearNonsplitInnerPlaneProductsTrivial :=
  linear_nonsplit_inner_plane_products_trivial_of_CA
    linear_nonsplit_all_dimension_inner_plane_local_core_centralization_of_CA

end CFSG.RankThree.PartOne
