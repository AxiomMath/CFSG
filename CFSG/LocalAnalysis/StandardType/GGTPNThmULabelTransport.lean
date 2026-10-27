module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIFunct
public import CFSG.Assembly.LargeEvenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

variable {K L : Type} [Field K] [Field L]

section Twisted

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (n : ℕ)

private def twistedFieldGens (K : Type) [Field K] : Set (LargeEvenChevGL A K) :=
  {g | g ∈ LargeEvenChevGroup A K ∧
    LargeEvenDiagramMap A K ρ *
        LargeEvenEntrywise A K (fun c => c ^ 2 ^ n) (zero_pow (pow_ne_zero n two_ne_zero))
          (g : Module.End K (LargeEvenChevModule A K)) =
      (g : Module.End K (LargeEvenChevModule A K)) * LargeEvenDiagramMap A K ρ}

private theorem largeEvenTwistedH_eq_closure :
    LargeEvenTwistedH A K ρ n =
      ⁅Subgroup.closure (twistedFieldGens A ρ n K),
        Subgroup.closure (twistedFieldGens A ρ n K)⁆ :=
  rfl

private theorem crossEnd_diagramMap (f : K ≃+* L) :
    MI.crossEnd A f (LargeEvenDiagramMap A K ρ) = LargeEvenDiagramMap A L ρ := by
  apply MI.end_ext
  intro b
  rw [MI.crossEnd_single]
  rcases b with i | α
  · simp only [LargeEvenDiagramMap, Finsupp.linearCombination_single, one_smul, MI.trf_hVec]
  · simp only [LargeEvenDiagramMap, Finsupp.linearCombination_single, one_smul, MI.trf_rootVec]

private theorem trf_mapRange_comm (f : K ≃+* L) (e : K → K) (e' : L → L)
    (he : e 0 = 0) (he' : e' 0 = 0) (hfe : ∀ c, f (e c) = e' (f c))
    (v : LargeEvenChevModule A K) :
    MI.trf A f (Finsupp.mapRange e he v) = Finsupp.mapRange e' he' (MI.trf A f v) := by
  ext x
  simp only [MI.trf_apply, Finsupp.mapRange_apply, hfe]

private theorem crossEnd_entrywise_pow (f : K ≃+* L)
    (g : Module.End K (LargeEvenChevModule A K)) :
    MI.crossEnd A f (LargeEvenEntrywise A K (fun c => c ^ 2 ^ n)
        (zero_pow (pow_ne_zero n two_ne_zero)) g) =
      LargeEvenEntrywise A L (fun c => c ^ 2 ^ n)
        (zero_pow (pow_ne_zero n two_ne_zero)) (MI.crossEnd A f g) := by
  apply MI.end_ext
  intro b
  rw [MI.crossEnd_single]
  simp only [LargeEvenEntrywise, Finsupp.linearCombination_single, one_smul, MI.crossEnd_single]
  rw [trf_mapRange_comm A f (fun c => c ^ 2 ^ n) (fun c => c ^ 2 ^ n) _ _
    (fun c => map_pow f c (2 ^ n))]

private theorem twistedFieldGens_map_le (f : K ≃+* L) :
    (Subgroup.closure (twistedFieldGens A ρ n K)).map (MI.chevCongr A f).toMonoidHom ≤
      Subgroup.closure (twistedFieldGens A ρ n L) := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  refine Subgroup.subset_closure ⟨MI.chevGroup_map_le A f ⟨g, hg.1, rfl⟩, ?_⟩
  have h := congrArg (MI.crossEnd A f) hg.2
  simp only [MI.crossEnd_mul, crossEnd_diagramMap, crossEnd_entrywise_pow] at h
  simpa only [MulEquiv.coe_toMonoidHom, MI.chevCongr_val] using h

private theorem twistedClosure_map_eq (f : K ≃+* L) :
    (Subgroup.closure (twistedFieldGens A ρ n K)).map (MI.chevCongr A f).toMonoidHom =
      Subgroup.closure (twistedFieldGens A ρ n L) := by
  refine le_antisymm (twistedFieldGens_map_le A ρ n f) ?_
  intro y hy
  refine Subgroup.mem_map.mpr ⟨(MI.chevCongr A f).symm y, ?_, by simp⟩
  have h := twistedFieldGens_map_le A ρ n (f.symm : L ≃+* K) ⟨y, hy, rfl⟩
  simpa only [MulEquiv.coe_toMonoidHom, MI.chevCongr_symm] using h

end Twisted

theorem largeEvenTwistedH_map_chevCongr {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (ρ : Equiv.Perm (Fin r)) (n : ℕ) (f : K ≃+* L) :
    (LargeEvenTwistedH A K ρ n).map (MI.chevCongr A f).toMonoidHom =
      LargeEvenTwistedH A L ρ n := by
  rw [largeEvenTwistedH_eq_closure A ρ n (K := K),
    largeEvenTwistedH_eq_closure A ρ n (K := L), Subgroup.map_commutator,
    twistedClosure_map_eq A ρ n f]

end CFSG.StandardType
