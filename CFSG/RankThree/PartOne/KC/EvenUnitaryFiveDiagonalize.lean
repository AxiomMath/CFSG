module

public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveEigen

public section

namespace CFSG.RankThree.PartOne.KCEvenUnitaryFive

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary

section Basis

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem exists_orthonormal_adapted_basis {ι : Type*} [Fintype ι] (W : ι → Submodule K (Fin 5 → K))
    (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤)
    (horth : ∀ i j, i ≠ j → ∀ v ∈ W i, ∀ w ∈ W j, idForm h 5 v w = 0) :
    ∃ (b : Module.Basis (Fin 5) K (Fin 5 → K)) (χ : Fin 5 → ι), (∀ k, b k ∈ W (χ k)) ∧
      ∀ k l, idForm h 5 (b k) (b l) = if k = l then 1 else 0 := by
  classical
  have hB := idForm_isSymm h 5
  have hBl := idForm_separatingLeft h 5
  have hsep : ∀ i, ((idForm h 5).domRestrict₁₂ (W i) (W i)).SeparatingLeft := by
    intro i v hv
    have hvz : ∀ u : Fin 5 → K, idForm h 5 (v : Fin 5 → K) u = 0 := by
      intro u
      have hu : u ∈ ⨆ j, W j := by rw [htop]; trivial
      refine Submodule.iSup_induction W (motive := fun u => idForm h 5 (v : Fin 5 → K) u = 0)
        hu (fun j u hu => ?_) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
      by_cases hij : j = i
      · subst hij
        exact hv ⟨u, hu⟩
      · exact horth i j (Ne.symm hij) v v.2 u hu
    exact Subtype.ext (hBl _ hvz)
  have : ∀ i, FiniteDimensional K (W i) := fun i => inferInstance
  choose e he using fun i => h.exists_orthonormal_basis
    (B := (idForm h 5).domRestrict₁₂ (W i) (W i)) (hB.domRestrict (W i)) (hsep i)
  have hint : DirectSum.IsInternal W := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    hind htop
  let bb := hint.collectedBasis e
  have hon : ∀ σ τ : Σ i, Fin (Module.finrank K (W i)),
      idForm h 5 (bb σ) (bb τ) = if σ = τ then 1 else 0 := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    simp only [bb, DirectSum.IsInternal.collectedBasis_coe]
    by_cases hij : i = j
    · subst hij
      have := he i a b
      simp only [LinearMap.domRestrict₁₂_apply] at this
      rw [this]
      simp
    · rw [horth i j hij _ (e i a).2 _ (e j b).2]
      simp [hij]
  have hcard : Fintype.card (Σ i, Fin (Module.finrank K (W i))) = 5 := by
    have := Module.finrank_eq_card_basis bb
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let eq := Fintype.equivFinOfCardEq hcard
  refine ⟨bb.reindex eq, fun k => (eq.symm k).1, fun k => ?_, fun k l => ?_⟩
  · rw [Module.Basis.reindex_apply]
    exact hint.collectedBasis_mem e (eq.symm k)
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hon]
    simp [eq.symm.injective.eq_iff]

end Basis

section Main

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_unitary_diagonalizing (h5 : 5 ∣ 2 ^ f + 1)
    (G : Subgroup (primeFormUnitary h (idGram K 5)))
    (hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hGnc : ¬ IsCyclic G)
    (hGpow : ∀ x ∈ G, x ^ 5 ∈ idScalarKernel h 5) :
    ∃ P : primeFormUnitary h (idGram K 5), ∀ x ∈ G,
      (((P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K).IsDiag := by
  classical
  have hfinK : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fintype ↥G := Fintype.ofFinite _
  let F : ↥G → Module.End K (Fin 5 → K) := fun x =>
    ((toLinU h 5 (x : primeFormUnitary h (idGram K 5)) :
      LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))
  have hFcomm : ∀ x y : ↥G, Commute (F x) (F y) := fun x y => by
    have h1 : Commute (toLinU h 5 (x : primeFormUnitary h (idGram K 5)))
        (toLinU h 5 (y : primeFormUnitary h (idGram K 5))) := by
      have := congrArg (toLinU h 5) (hGcomm x x.2 y y.2)
      rw [map_mul, map_mul] at this
      exact this
    exact h1.units_val
  have hsemi : ∀ x : ↥G, (F x).IsSemisimple := fun x => by
    obtain ⟨c, hcq, hc⟩ := hGpow x x.2
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (separable_X_pow_sub_C (c : K) (five_ne_zero h) c.ne_zero).squarefree
      (aeval_toLinU_eq_zero h hc)
  have htop : ∀ x : ↥G, ⨆ μ, (F x).maxGenEigenspace μ = ⊤ := fun x =>
    ((hsemi x).iSup_maxGenEigenspace_eq_top_iff).mpr
      (iSup_eigenspace_eq_top h h5 G hGcomm hGnc hGpow x.2)
  have hjoint :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      F (fun x y _ => hFcomm x y) htop
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hFcomm j i) φ)
  let W : (↥G → K) → Submodule K (Fin 5 → K) := fun χ =>
    ⨅ x, Module.End.eigenspace (F x) (χ x)
  have hW : ∀ χ, ⨅ x, (F x).maxGenEigenspace (χ x) = W χ := fun χ =>
    iInf_congr fun x => (hsemi x).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _
  have hWeig : ∀ χ, ∀ v ∈ W χ, ∀ x : ↥G, F x v = χ x • v := fun χ v hv x =>
    Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv x)
  have hWind : iSupIndep W := by
    have := hind
    simp only [hW] at this
    exact this
  have hWtop : ⨆ χ, W χ = ⊤ := by
    have := hjoint
    simp only [hW] at this
    exact this
  have horth : ∀ χ χ' : ↥G → K, χ ≠ χ' → ∀ v ∈ W χ, ∀ w ∈ W χ', idForm h 5 v w = 0 := by
    intro χ χ' hne v hv w hw
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, LinearMap.zero_apply]
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
    have hbar : h.bar (χ x) * χ x = 1 :=
      bar_mul_eq_one_of_eigenvalue h h5 (hGpow x x.2) hv0 (hWeig χ v hv x)
    have hbar' : h.bar (χ' x) * χ' x = 1 :=
      bar_mul_eq_one_of_eigenvalue h h5 (hGpow x x.2) hw0 (hWeig χ' w hw x)
    have hiso := (mem_sesqUnitaryGroup.mp (toLinU_mem (x : primeFormUnitary h (idGram K 5)))) v w
    have hFx : ((toLinU h 5 (x : primeFormUnitary h (idGram K 5)) :
        LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) = F x := rfl
    rw [hFx] at hiso
    change idForm h 5 ((F x) v) ((F x) w) = idForm h 5 v w at hiso
    rw [hWeig χ v hv x, hWeig χ' w hw x] at hiso
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at hiso
    have hb0 : h.bar (χ x) ≠ 0 := left_ne_zero_of_mul_eq_one hbar
    have hne' : h.bar (χ x) * χ' x ≠ 1 := by
      intro h1
      exact hx (mul_left_cancel₀ hb0 (hbar.trans h1.symm))
    have h2 : (h.bar (χ x) * χ' x - 1) * idForm h 5 v w = 0 := by linear_combination hiso
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne')
  obtain ⟨b, χ₀, hbW, hon⟩ := exists_orthonormal_adapted_basis h W hWind hWtop horth
  let Pm : Matrix (Fin 5) (Fin 5) K := Matrix.of fun r k => b k r
  have hPm : (Pm.map h.bar)ᵀ * Pm = 1 := by
    ext k l
    have := hon k l
    rw [gramForm_apply] at this
    simp only [idGram, Units.val_one, Matrix.one_mulVec] at this
    simpa [Matrix.mul_apply, Matrix.one_apply, Pm, dotProduct] using this
  have hPm' : Pm * (Pm.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hPm
  let P : primeFormUnitary h (idGram K 5) :=
    ⟨⟨Pm, (Pm.map h.bar)ᵀ, hPm', hPm⟩, by
      rw [mem_primeFormUnitary]
      simpa [idGram] using hPm⟩
  refine ⟨P, fun x hx => ?_⟩
  have hxP : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Pm =
      Pm * diagonal (fun k => χ₀ k ⟨x, hx⟩) := by
    ext r k
    have h1 := hWeig (χ₀ k) (b k) (hbW k) ⟨x, hx⟩
    have h2 := congrFun h1 r
    have h3 : (F ⟨x, hx⟩ (b k)) r =
        (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ b k) r := rfl
    rw [h3] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h4 : (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Pm) r k =
        (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ b k) r := rfl
    rw [Matrix.mul_diagonal, h4, h2]
    change _ = b k r * _
    ring
  have : ((P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      ((P : GL (Fin 5) K)⁻¹ * (x : GL (Fin 5) K) * (P : GL (Fin 5) K)) := rfl
  rw [this, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  change (((P : GL (Fin 5) K)⁻¹ : GL (Fin 5) K).val *
    (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Pm)).IsDiag
  rw [hxP, ← Matrix.mul_assoc]
  have hP1 : (((P : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Pm = 1 :=
    Units.inv_mul _
  rw [hP1, Matrix.one_mul]
  exact Matrix.isDiag_diagonal _

end Main

end CFSG.RankThree.PartOne.KCEvenUnitaryFive
