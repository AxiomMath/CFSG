module

public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.LocalAnalysis.StandardType.PhanEStdTwE6Nodes
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley

public noncomputable section



namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.PsiDiagChar CFSG.StandardType.RankOneXfer

variable {k K : Type} [Field k] [Field K]

theorem fixed_root_torus_scalar (theta : K →+* K) (e : k →+* K)
    (i : Fin (Tag.rank .E6))
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* fixedGroup K theta)
    (hu : ∀ t, (phi (sl2Upper t) : e6Data_valid.minGroup K) =
      e6Data_valid.xm K (Pi.single i 1) (e t))
    (hup : (sl2UpperUniSub k).map phi =
      (twistedDatum K theta).rootGroup (proj (Pi.single i 1)))
    (h : fixedGroup K theta) (hh : h ∈ ggTorus (twistedDatum K theta)) :
    ∃ c : k, ∀ t : k, h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t)) := by
  let A := Module.End K (Fin e6Data.d →₀ K)
  letI : Algebra k A := Algebra.compHom A e
  let ι : fixedGroup K theta →* A :=
    { toFun := fun g => e6Data_valid.endo K (g : e6Data_valid.minGroup K)
      map_one' := e6Data_valid.endo_one K
      map_mul' := fun g g' => e6Data_valid.endo_mul K _ _ }
  have hι : Function.Injective ι := fun g g' heq =>
    Subtype.ext (e6Data_valid.endo_injective K heq)
  let y : k → fixedGroup K theta := fun t => phi (sl2Upper t)
  let X := (twistedDatum K theta).rootGroup (proj (Pi.single i 1))
  have hX : ∀ g, g ∈ X ↔ ∃ t, y t = g := by
    intro g
    dsimp only [X]
    rw [← hup]
    constructor
    · rintro ⟨M, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact Subgroup.mem_map.2 ⟨sl2Upper t, ⟨t, rfl⟩, rfl⟩
  have haff : ∀ t, ι (y t) = 1 + t • e6Data.rootOp K (Pi.single i 1) := by
    intro t
    change e6Data_valid.endo K (phi (sl2Upper t) : e6Data_valid.minGroup K) = _
    rw [hu, e6Data_valid.endo_xm]
    simp only [Algebra.smul_def, Algebra.compHom_algebraMap_eq, RingHom.comp_apply]
  have hγ : proj (Pi.single i 1) ∈ (twistedDatum K theta).roots := by
    rw [twistedDatum_roots]
    exact isRoot_proj (isRoot_single .E6 i)
  have hhX : h ∈ Subgroup.normalizer (X : Set (fixedGroup K theta)) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh _ hγ
  exact PsiDiag.conj_eq_of_affine ι hι hX haff hhX

theorem fixed_root_lower_image (theta : K →+* K) (e : k →+* K)
    (he : ∀ t, theta (e t) = e t)
    (hfixed : ∀ t, theta t = t → ∃ c, e c = t)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i)
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* fixedGroup K theta)
    (hl : ∀ t, (phi (sl2Lower t) : e6Data_valid.minGroup K) =
      e6Data_valid.xm K (-Pi.single i 1) (e t)) :
    Set.range (fun t => phi (sl2Lower t)) =
      ((twistedDatum K theta).rootGroup (-proj (Pi.single i 1)) : Set (fixedGroup K theta)) := by
  have hr : IsRoot .E6 (-Pi.single i 1) := isRoot_neg_single .E6 i
  have hρ : rho (-Pi.single i 1) = -Pi.single i 1 := by rw [rho_neg_single, hi]
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    change phi (sl2Lower t) ∈ twistedRootGroup K theta (-proj (Pi.single i 1))
    have ht := (mem_twistedRootGroup_iff_of_fixed theta hr rfl hρ (phi (sl2Lower t))).2
      ⟨e t, he t, hl t⟩
    simpa only [map_neg] using ht
  · intro hg
    change g ∈ twistedRootGroup K theta (-proj (Pi.single i 1)) at hg
    have hg' : g ∈ twistedRootGroup K theta (proj (-Pi.single i 1)) := by
      simpa only [map_neg] using hg
    obtain ⟨t, ht, hgt⟩ := (mem_twistedRootGroup_iff_of_fixed theta hr rfl hρ g).1 hg'
    obtain ⟨c, rfl⟩ := hfixed t ht
    exact ⟨c, Subtype.ext ((hl c).trans hgt.symm)⟩

section ModelData

variable [Finite K] [CharP K 2]

theorem exists_e6_fixed_root_model_data (σ : K ≃+* K) (e : k →+* K)
    (hfix : ∀ t : K, σ t = t ↔ t ∈ Set.range e)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i) :
    ∃ phi : Matrix.SpecialLinearGroup (Fin 2) k →* fixedGroup K σ.toRingHom,
      Function.Injective phi ∧
      (∀ t, (phi (sl2Upper t) : e6Data_valid.minGroup K) = e6Data_valid.xm K (Pi.single i 1) (e t)) ∧
      (∀ t, (phi (sl2Lower t) : e6Data_valid.minGroup K) = e6Data_valid.xm K (-Pi.single i 1) (e t)) ∧
      (sl2UpperUniSub k).map phi = (twistedDatum K σ.toRingHom).rootGroup (proj (Pi.single i 1)) ∧
      (∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus (twistedDatum K σ.toRingHom)) ∧
      (∀ h ∈ ggTorus (twistedDatum K σ.toRingHom), ∃ c : k,
        ∀ t : k, h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t))) ∧
      Set.range (fun t => phi (sl2Lower t)) =
        ((twistedDatum K σ.toRingHom).rootGroup (-proj (Pi.single i 1)) :
          Set (fixedGroup K σ.toRingHom)) := by
  obtain ⟨phi, hphi, hu, hl, hup, hdiag, -⟩ :=
    exists_e6_fixed_primitive_root_with_params σ e hfix i hi
  refine ⟨phi, hphi, hu, hl, hup, hdiag, ?_, ?_⟩
  · intro h hh
    exact fixed_root_torus_scalar σ.toRingHom e i phi hu hup h hh
  · exact fixed_root_lower_image σ.toRingHom e (fun t => (hfix _).2 ⟨t, rfl⟩)
      (fun t ht => (hfix t).1 ht) i hi phi hl

theorem exists_e6_fixed_selected_root (σ : K ≃+* K) (e : k →+* K)
    (hfix : ∀ t : K, σ t = t ↔ t ∈ Set.range e)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i) :
    ∃ model : SelectedRoot.SelectedSL2Model (twistedDatum K σ.toRingHom) k (proj (Pi.single i 1)),
      model.phi.range = ggRootLevi (twistedDatum K σ.toRingHom) (proj (Pi.single i 1)) ∧
      (∀ t, (model.phi (sl2Upper t) : e6Data_valid.minGroup K) =
        e6Data_valid.xm K (Pi.single i 1) (e t)) ∧
      ∀ t, (model.phi (sl2Lower t) : e6Data_valid.minGroup K) =
        e6Data_valid.xm K (-Pi.single i 1) (e t) := by
  obtain ⟨phi, hphi, hu, hl, hup, hdiag, hscalar, hlower⟩ :=
    exists_e6_fixed_root_model_data σ e hfix i hi
  have hroot : proj (Pi.single i 1) ∈ (twistedDatum K σ.toRingHom).roots := by
    rw [twistedDatum_roots]
    exact isRoot_proj (isRoot_single .E6 i)
  let model := SelectedRoot.SelectedSL2Model.ofRootMap (twistedDatum K σ.toRingHom)
    (proj (Pi.single i 1)) hroot phi hphi hup hdiag hscalar
  refine ⟨model, ?_, hu, hl⟩
  exact SelectedRoot.SelectedSL2Model.ofRootMap_range (twistedDatum K σ.toRingHom)
    (proj (Pi.single i 1)) hroot phi hphi hup hdiag hscalar hlower

end ModelData

section NativeModel

open CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld.LieEmbed

theorem exists_selectedSL2Model_twistedE6_fixed {f : ℕ} (hf : 1 ≤ f)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i) :
    ∃ model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 f).D (GaloisField 2 f)
      (proj (Pi.single i 1)),
      model.phi.range = ggRootLevi (ggU .twistedE6 0 f).D (proj (Pi.single i 1)) ∧
      (∀ t, (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype (model.phi (sl2Upper t)) =
        e6Data_valid.xm (GaloisField 2 (2 * f)) (Pi.single i 1) (gfEmbed 2 f hf t)) ∧
      ∀ t, (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype (model.phi (sl2Lower t)) =
        e6Data_valid.xm (GaloisField 2 (2 * f)) (-Pi.single i 1) (gfEmbed 2 f hf t) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_e6_fixed_selected_root (frobQEquiv hf) (gfEmbed 2 f hf).toRingHom
    (fun t => frobQ_eq_iff_mem_range 2 f hf t) i hi

theorem twistedE6_fixed_simple_long {f : ℕ}
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i) :
    GGLongRoot (ggU .twistedE6 0 f).D (proj (Pi.single i 1)) := by
  change GGLongRoot (CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f))
    (proj (Pi.single i 1))
  have hc : ∀ j : Fin (Tag.rank .E6), rhoPerm j = j → j = 1 ∨ j = 3 := by
    decide +kernel
  rcases hc i hi with rfl | rfl
  · have hp : proj (Pi.single (1 : Fin (Tag.rank .E6)) 1) =
        Pi.single (0 : Fin (Tag.rank .F4)) 1 := by
      funext j
      fin_cases j <;> rfl
    rw [hp]
    exact (LieKnownR2.Short.f4_ggLongRoot_single_iff (GaloisField 2 f) 0).2
      (by change (0 : ℕ) ≤ 1; omega)
  · have hp : proj (Pi.single (3 : Fin (Tag.rank .E6)) 1) =
        Pi.single (1 : Fin (Tag.rank .F4)) 1 := by
      funext j
      fin_cases j <;> rfl
    rw [hp]
    exact (LieKnownR2.Short.f4_ggLongRoot_single_iff (GaloisField 2 f) 1).2
      (by change (1 : ℕ) ≤ 1; omega)

theorem exists_selectedSL2Model_twistedE6_fixed_comp {G : Type} [Group G]
    {f : ℕ} (hf : 1 ≤ f) (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i)
    (lambda : (ggU .twistedE6 0 f).K →* G) :
    ∃ model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 f).D (GaloisField 2 f)
      (proj (Pi.single i 1)),
      (lambda.comp model.phi).range =
        (ggRootLevi (ggU .twistedE6 0 f).D (proj (Pi.single i 1))).map lambda := by
  obtain ⟨model, hmodel, -, -⟩ := exists_selectedSL2Model_twistedE6_fixed hf i hi
  refine ⟨model, ?_⟩
  rw [MonoidHom.range_comp, hmodel]

end NativeModel

end CFSG.ClassicalInvolution.Phan.PhanE
