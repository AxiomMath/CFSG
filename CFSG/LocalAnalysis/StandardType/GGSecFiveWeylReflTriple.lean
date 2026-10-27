module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCR3OfPump
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylTripleTransport
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleRoots
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxProdHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.RootSystem

private theorem ct_wt_exists_cartan {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : CoxeterMatrix ι) (hM : GGIsWeylMatrix M)
    (hG2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) :
    ∃ (C : Matrix ι ι ℤ) (hC : TauCeti.IsFiniteType C), M = coxeterMatrix hC := by
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ |
    ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2Eq⟩
  · have hFT : TauCeti.IsFiniteType (Matrix.reindex e e (CartanMatrix.A n)) := by
      rw [Matrix.reindex_apply]
      exact (TauCeti.isFiniteType_cartanMatrix_A n).submatrix e.symm.injective
    refine ⟨_, hFT, ?_⟩
    rw [hA]
    exact (coxeterMatrix_eq_of_ggIntCartan hFT ((ggIntCartan_A n).reindex e)).symm
  · have hFT : TauCeti.IsFiniteType (Matrix.reindex e e (CartanMatrix.B n)) := by
      rw [Matrix.reindex_apply]
      exact (TauCeti.isFiniteType_cartanMatrix_B n).submatrix e.symm.injective
    refine ⟨_, hFT, ?_⟩
    rw [hB]
    exact (coxeterMatrix_eq_of_ggIntCartan hFT ((ggIntCartan_B n).reindex e)).symm
  · have hFT : TauCeti.IsFiniteType (Matrix.reindex e e (CartanMatrix.D n)) := by
      rw [Matrix.reindex_apply]
      exact (TauCeti.isFiniteType_cartanMatrix_D n).submatrix e.symm.injective
    refine ⟨_, hFT, ?_⟩
    rw [hD]
    exact (coxeterMatrix_eq_of_ggIntCartan hFT ((ggIntCartan_D n).reindex e)).symm
  · have hFT : TauCeti.IsFiniteType (Matrix.reindex e e (CartanMatrix.E 6)) := by
      rw [Matrix.reindex_apply]
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
      rw [TauCeti.DynkinType.cartanMatrix_E6] at h
      exact h.submatrix e.symm.injective
    refine ⟨_, hFT, ?_⟩
    rw [hE6]
    exact (coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_E₆.reindex e)).symm
  · have hFT : TauCeti.IsFiniteType (Matrix.reindex e e (CartanMatrix.E 7)) := by
      rw [Matrix.reindex_apply]
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
      rw [TauCeti.DynkinType.cartanMatrix_E7] at h
      exact h.submatrix e.symm.injective
    refine ⟨_, hFT, ?_⟩
    rw [hE7]
    exact (coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_E₇.reindex e)).symm
  · have hFT : TauCeti.IsFiniteType (Matrix.reindex e e (CartanMatrix.E 8)) := by
      rw [Matrix.reindex_apply]
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
      rw [TauCeti.DynkinType.cartanMatrix_E8] at h
      exact h.submatrix e.symm.injective
    refine ⟨_, hFT, ?_⟩
    rw [hE8]
    exact (coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_E₈.reindex e)).symm
  · have hFT : TauCeti.IsFiniteType (Matrix.reindex e e CartanMatrix.F₄) := by
      rw [Matrix.reindex_apply]
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_F4
      rw [TauCeti.DynkinType.cartanMatrix_F4] at h
      exact h.submatrix e.symm.injective
    refine ⟨_, hFT, ?_⟩
    rw [hF4]
    exact (coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_F₄.reindex e)).symm
  · exact absurd ⟨e, hG2Eq⟩ hG2

theorem ggWeylReflTripleInput_holds : GGWeylReflTripleInput := by
  intro G _ _ p Bs A hp hp2 hEl hNT hW hG2 r₁ hr₁ r₂ hr₂ s hs hR₁ hR₂ hS h3
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  have hFin : Finite ι := ggIsWeylMatrix_finite hM
  classical
  have hFintype : Fintype ι := Fintype.ofFinite ι
  have hG2' : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, rfl⟩
    exact hG2 (GGWeylOfType.of_reindex (M := CoxeterMatrix.G₂) (e := e) (A := A) ⟨f, hf⟩)
  obtain ⟨C, hC, hEq⟩ := ct_wt_exists_cartan M hM hG2'
  subst M
  obtain ⟨i₁, g₁, h₁⟩ := ggRootRefl_of_noTransvection_in G p Bs A hp hp2 hEl hNT
    ι (coxeterMatrix hC) hM hG2' f hf ⟨r₁, hr₁⟩ hR₁
  obtain ⟨i₂, g₂, h₂⟩ := ggRootRefl_of_noTransvection_in G p Bs A hp hp2 hEl hNT
    ι (coxeterMatrix hC) hM hG2' f hf ⟨r₂, hr₂⟩ hR₂
  obtain ⟨i₃, g₃, h₃⟩ := ggRootRefl_of_noTransvection_in G p Bs A hp hp2 hEl hNT
    ι (coxeterMatrix hC) hM hG2' f hf ⟨s, hs⟩ hS
  let t₁ : (coxeterMatrix hC).Group := g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹
  let t₂ : (coxeterMatrix hC).Group := g₂ * (coxeterMatrix hC).simple i₂ * g₂⁻¹
  let t₃ : (coxeterMatrix hC).Group := g₃ * (coxeterMatrix hC).simple i₃ * g₃⁻¹
  let F : (coxeterMatrix hC).Group →* MulAut ↥Bs := A.subtype.comp f
  have ht₁ : F t₁ = r₁ := by
    have h := congrArg Subtype.val h₁
    simpa [F, t₁] using h.symm
  have ht₂ : F t₂ = r₂ := by
    have h := congrArg Subtype.val h₂
    simpa [F, t₂] using h.symm
  have ht₃ : F t₃ = s := by
    have h := congrArg Subtype.val h₃
    simpa [F, t₃] using h.symm
  have hF : Function.Injective F := by
    simpa [F] using A.subtype_injective.comp f.injective
  have hclos : Subgroup.closure ({r₁, r₂, s} : Set (MulAut ↥Bs)) =
      (Subgroup.closure ({t₁, t₂, t₃} : Set (coxeterMatrix hC).Group)).map F := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨t₁, Or.inl rfl, ht₁⟩
      · exact ⟨t₂, Or.inr (Or.inl rfl), ht₂⟩
      · exact ⟨t₃, Or.inr (Or.inr rfl), ht₃⟩
    · rintro ⟨y, (rfl | rfl | rfl), hFy⟩
      · exact Or.inl (hFy.symm.trans ht₁)
      · exact Or.inr (Or.inl (hFy.symm.trans ht₂))
      · exact Or.inr (Or.inr (hFy.symm.trans ht₃))
  have hcard : Nat.card (Subgroup.closure ({r₁, r₂, s} : Set (MulAut ↥Bs))) =
      Nat.card (Subgroup.closure ({t₁, t₂, t₃} : Set (coxeterMatrix hC).Group)) := by
    rw [hclos, Subgroup.card_map_of_injective hF]
  have htprod : F (t₁ * t₂) = r₁ * r₂ := by rw [map_mul, ht₁, ht₂]
  have h3t : orderOf (t₁ * t₂) = 3 := by
    rw [← orderOf_injective F hF (t₁ * t₂), htprod, h3]
  have hord : ∀ (i j : ι) (g h : (coxeterMatrix hC).Group),
      orderOf (g * (coxeterMatrix hC).simple i * g⁻¹ *
        (h * (coxeterMatrix hC).simple j * h⁻¹)) ≤ 4 :=
    ggSecFiveCoxProdInput_holds ι (coxeterMatrix hC) hM hG2'
  have h48 : Nat.card (Subgroup.closure ({t₁, t₂, t₃} :
      Set (coxeterMatrix hC).Group)) ∣ 48 :=
    CoxTriple.coxTriple_card_dvd_48 hC hord i₁ i₂ i₃ g₁ g₂ g₃ h3t
  rw [hcard]
  exact h48

end CFSG.StandardType

end
