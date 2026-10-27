module

public import CFSG.LocalAnalysis.StandardType.GGRankOneRootMatch

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.StandardType.PsiDiag
  CFSG.StandardType.PsiDiagChar CFSG.StandardType.RankOneXfer

structure SelectedSL2Model {K : Type*} [Group K] (D : UniversalRootDatum K) (k : Type*)
    [Field k] (gamma : Fin D.rank → ℤ) where
  root_mem : gamma ∈ D.roots
  phi : Matrix.SpecialLinearGroup (Fin 2) k →* K
  injective : Function.Injective phi
  upper_eq : (sl2UpperUniSub k).map phi = D.rootGroup gamma
  diag_mem : ∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus D
  scalar : ∀ h ∈ ggTorus D, ∃ c : kˣ, ∀ t : k,
    h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper ((c : k) * t))

variable {K K' G : Type*} [Group K] [Group K'] [Group G]

private lemma ker_conj_comp_le_center (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) (u : K) :
    (ψ.comp (MulAut.conj u).toMonoidHom).ker ≤ Subgroup.center K := by
  intro y hy
  have hy1 : ψ ((MulAut.conj u) y) = 1 := MonoidHom.mem_ker.mp hy
  have hy' : u * y * u⁻¹ ∈ Subgroup.center K := by
    apply hker
    rw [MonoidHom.mem_ker]
    rw [MulAut.conj_apply] at hy1
    exact hy1
  rw [Subgroup.mem_center_iff] at hy' ⊢
  intro z
  have hcy : y = u⁻¹ * (u * y * u⁻¹) * u := by group
  rw [hcy]
  have hcu : u⁻¹ * (u * y * u⁻¹) * u = u * y * u⁻¹ := by
    rw [mul_assoc, ← hy' u, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hcu]
  exact hy' z

theorem torusClause_of_sl2Embedding
    {D : UniversalRootDatum K} {D' : UniversalRootDatum K'}
    {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
    {gamma : Fin D.rank → ℤ} {delta : Fin D'.rank → ℤ}
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* K)
    (hupper : (sl2UpperUniSub k).map phi = D.rootGroup gamma)
    (hdiag : ∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus D)
    (model' : SelectedSL2Model D' k' delta)
    (ψ : K →* G) (ψ' : K' →* G) (u : K)
    (hΦ : Function.Injective ((ψ.comp (MulAut.conj u).toMonoidHom).comp phi))
    (hΦ' : Function.Injective (ψ'.comp model'.phi))
    (hY : (sl2UpperUniSub k).map ((ψ.comp (MulAut.conj u).toMonoidHom).comp phi) =
      (sl2UpperUniSub k').map (ψ'.comp model'.phi))
    (hS : ((ψ.comp (MulAut.conj u).toMonoidHom).comp phi).range =
      (ψ'.comp model'.phi).range) :
    ∀ h' ∈ ggTorus D', ∃ h ∈ ggTorus D, ∀ z ∈ D.rootGroup gamma,
      ∀ z' ∈ D'.rootGroup delta,
        ψ' z' = ψ (u * z * u⁻¹) → ψ' (h' * z' * h'⁻¹) = ψ (u * (h * z * h⁻¹) * u⁻¹) := by
  let Φ₁ : Matrix.SpecialLinearGroup (Fin 2) k →* G :=
    (ψ.comp (MulAut.conj u).toMonoidHom).comp phi
  let Φ' : Matrix.SpecialLinearGroup (Fin 2) k' →* G := ψ'.comp model'.phi
  have hΦ₁ : Function.Injective Φ₁ := hΦ
  have hY' : (sl2UpperUniSub k).map Φ₁ = (sl2UpperUniSub k').map Φ' := hY
  have hS' : Φ₁.range = Φ'.range := hS
  intro h' hh'
  obtain ⟨c, hc⟩ := model'.scalar h' hh'
  obtain ⟨ζ, hζ⟩ := PsiDiagChar.exists_sq_eq c
  have hζval : ((ζ : k') ^ 2) = (c : k') := by
    have h := congrArg (fun s : k'ˣ => (s : k')) hζ
    simpa using h
  have hd' : ∀ t : k',
      Φ' (sl2Diag ζ) * Φ' (sl2Upper t) * (Φ' (sl2Diag ζ))⁻¹ =
        Φ' (sl2Upper ((c : k') * t)) := by
    intro t
    calc Φ' (sl2Diag ζ) * Φ' (sl2Upper t) * (Φ' (sl2Diag ζ))⁻¹
        = Φ' (sl2Diag ζ * sl2Upper t * (sl2Diag ζ)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = Φ' (sl2Upper (((ζ : k') ^ 2) * t)) := by rw [sl2Diag_conj_sl2Upper]
      _ = Φ' (sl2Upper ((c : k') * t)) := by rw [hζval]
  have hd₁ : Φ' (sl2Diag ζ) ∈ Φ₁.range := by
    rw [hS']
    exact ⟨sl2Diag ζ, rfl⟩
  obtain ⟨τ, hτ⟩ := hd₁
  have hconj_exists : ∀ t : k, ∃ t' : k, τ * sl2Upper t * τ⁻¹ = sl2Upper t' := by
    intro t
    have hmem : Φ₁ (sl2Upper t) ∈ (sl2UpperUniSub k').map Φ' := by
      rw [← hY']
      exact Subgroup.mem_map.mpr
        ⟨sl2Upper t, mem_sl2UpperUniSub_iff.mpr ⟨t, rfl⟩, rfl⟩
    obtain ⟨M, hM, hMΦ⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨e, rfl⟩ := mem_sl2UpperUniSub_iff.mp hM
    have hconj : Φ₁ (τ * sl2Upper t * τ⁻¹) = Φ' (sl2Upper ((c : k') * e)) := by
      calc Φ₁ (τ * sl2Upper t * τ⁻¹)
          = Φ₁ τ * Φ₁ (sl2Upper t) * (Φ₁ τ)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = Φ' (sl2Diag ζ) * Φ' (sl2Upper e) * (Φ' (sl2Diag ζ))⁻¹ := by
              rw [hτ, ← hMΦ]
        _ = Φ' (sl2Diag ζ * sl2Upper e * (sl2Diag ζ)⁻¹) := by
              rw [map_mul, map_mul, map_inv]
        _ = Φ' (sl2Upper (((ζ : k') ^ 2) * e)) := by rw [sl2Diag_conj_sl2Upper]
        _ = Φ' (sl2Upper ((c : k') * e)) := by rw [hζval]
    have hmem2 : Φ' (sl2Upper ((c : k') * e)) ∈ (sl2UpperUniSub k).map Φ₁ := by
      rw [hY']
      exact Subgroup.mem_map.mpr
        ⟨sl2Upper ((c : k') * e), mem_sl2UpperUniSub_iff.mpr ⟨(c : k') * e, rfl⟩, rfl⟩
    obtain ⟨M', hM', hM'Φ⟩ := Subgroup.mem_map.mp hmem2
    obtain ⟨t', rfl⟩ := mem_sl2UpperUniSub_iff.mp hM'
    refine ⟨t', hΦ₁ ?_⟩
    rw [hconj, hM'Φ]
  obtain ⟨a, ha⟩ := exists_sq_conj_of_conj_upper hconj_exists
  refine ⟨phi (sl2Diag a), hdiag a, ?_⟩
  intro z hz z' hz' hzz'
  have hz_mem : z ∈ (sl2UpperUniSub k).map phi := by rwa [hupper]
  obtain ⟨M, hM, hMz⟩ := Subgroup.mem_map.mp hz_mem
  obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hM
  have hz_eq : z = phi (sl2Upper t) := hMz.symm
  have hz'_mem : z' ∈ (sl2UpperUniSub k').map model'.phi := by rwa [model'.upper_eq]
  obtain ⟨M', hM', hM'z⟩ := Subgroup.mem_map.mp hz'_mem
  obtain ⟨t', rfl⟩ := mem_sl2UpperUniSub_iff.mp hM'
  have hz'_eq : z' = model'.phi (sl2Upper t') := hM'z.symm
  have hS_eq : ψ' z' = Φ₁ (sl2Upper t) := by
    rw [hzz', hz_eq]
    rfl
  have hleft : ψ' (h' * z' * h'⁻¹) = Φ₁ (sl2Upper ((a : k) ^ 2 * t)) := by
    calc ψ' (h' * z' * h'⁻¹)
        = ψ' (h' * model'.phi (sl2Upper t') * h'⁻¹) := by rw [← hz'_eq]
      _ = ψ' (model'.phi (sl2Upper ((c : k') * t'))) := by rw [hc t']
      _ = ψ' (model'.phi (sl2Diag ζ * sl2Upper t' * (sl2Diag ζ)⁻¹)) := by
            rw [sl2Diag_conj_sl2Upper, hζval]
      _ = ψ' (model'.phi (sl2Diag ζ) * model'.phi (sl2Upper t') *
            (model'.phi (sl2Diag ζ))⁻¹) := by
            congr 1
            rw [map_mul, map_mul, map_inv]
      _ = ψ' (model'.phi (sl2Diag ζ)) * ψ' (model'.phi (sl2Upper t')) *
            (ψ' (model'.phi (sl2Diag ζ)))⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = Φ' (sl2Diag ζ) * ψ' z' * (Φ' (sl2Diag ζ))⁻¹ := by
            rw [← hz'_eq]
            rfl
      _ = Φ' (sl2Diag ζ) * Φ₁ (sl2Upper t) * (Φ' (sl2Diag ζ))⁻¹ := by rw [hS_eq]
      _ = Φ₁ τ * Φ₁ (sl2Upper t) * (Φ₁ τ)⁻¹ := by rw [← hτ]
      _ = Φ₁ (τ * sl2Upper t * τ⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = Φ₁ (sl2Upper ((a : k) ^ 2 * t)) := by rw [ha t]
  have hright : ψ (u * (phi (sl2Diag a) * z * (phi (sl2Diag a))⁻¹) * u⁻¹) =
      Φ₁ (sl2Upper ((a : k) ^ 2 * t)) := by
    have hz_conj : phi (sl2Diag a) * phi (sl2Upper t) *
        (phi (sl2Diag a))⁻¹ = phi (sl2Upper ((a : k) ^ 2 * t)) := by
      calc phi (sl2Diag a) * phi (sl2Upper t) * (phi (sl2Diag a))⁻¹
          = phi (sl2Diag a * sl2Upper t * (sl2Diag a)⁻¹) := by
            rw [map_mul, map_mul, map_inv]
        _ = phi (sl2Upper ((a : k) ^ 2 * t)) := by rw [sl2Diag_conj_sl2Upper]
    rw [hz_eq, hz_conj]
    rfl
  rw [hleft, hright]

theorem rootMatch_of_sl2Range_eq
    {D : UniversalRootDatum K} {D' : UniversalRootDatum K'}
    {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
    {gamma : Fin D.rank → ℤ} {delta : Fin D'.rank → ℤ}
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* K) (hphi : Function.Injective phi)
    (hupper : (sl2UpperUniSub k).map phi = D.rootGroup gamma)
    (hdiag : ∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus D)
    (model' : SelectedSL2Model D' k' delta)
    (ψ : K →* G) (ψ' : K' →* G)
    (hker : ψ.ker ≤ Subgroup.center K) (hker' : ψ'.ker ≤ Subgroup.center K')
    (u₀ : K)
    (hS : ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp phi).range =
      (ψ'.comp model'.phi).range) :
    ∃ u : K, GGRootMatch D D' ψ ψ' delta gamma u := by
  let θ₀ : K →* G := ψ.comp (MulAut.conj u₀).toMonoidHom
  let Φ₀ : Matrix.SpecialLinearGroup (Fin 2) k →* G := θ₀.comp phi
  let Φ' : Matrix.SpecialLinearGroup (Fin 2) k' →* G := ψ'.comp model'.phi
  have hθker : θ₀.ker ≤ Subgroup.center K := by
    change (ψ.comp (MulAut.conj u₀).toMonoidHom).ker ≤ Subgroup.center K
    exact ker_conj_comp_le_center ψ hker u₀
  have hΦ₀ : Function.Injective Φ₀ := by
    change Function.Injective (θ₀.comp phi)
    exact PsiDiag.injective_comp_of_ker_le_center phi hphi θ₀ hθker
  have hΦ' : Function.Injective Φ' := by
    change Function.Injective (ψ'.comp model'.phi)
    exact PsiDiag.injective_comp_of_ker_le_center model'.phi model'.injective ψ' hker'
  have hr : Φ₀.range = Φ'.range := by
    change ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp phi).range =
      (ψ'.comp model'.phi).range
    exact hS
  obtain ⟨σ, hσ⟩ := exists_conj_sl2UpperUniSub_map_eq Φ₀ Φ' hΦ₀ hΦ' hr
  let u : K := u₀ * phi σ
  let Φ₁ : Matrix.SpecialLinearGroup (Fin 2) k →* G :=
    (ψ.comp (MulAut.conj u).toMonoidHom).comp phi
  have hφconj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) k,
      phi (σ * M * σ⁻¹) = phi σ * phi M * (phi σ)⁻¹ := by
    intro M
    rw [map_mul, map_mul, map_inv]
  have hΦ₁eq : Φ₁ = Φ₀.comp (MulAut.conj σ).toMonoidHom := by
    ext M
    change ψ ((MulAut.conj u) (phi M)) = θ₀ (phi ((MulAut.conj σ) M))
    rw [MulAut.conj_apply, MulAut.conj_apply]
    change ψ (u * phi M * u⁻¹) = ψ (u₀ * phi (σ * M * σ⁻¹) * u₀⁻¹)
    rw [hφconj M]
    rw [show u = u₀ * phi σ from rfl]
    congr 1
    group
  have hΦ₁ : Function.Injective Φ₁ := by
    intro M N hMN
    rw [hΦ₁eq, MonoidHom.comp_apply, MonoidHom.comp_apply] at hMN
    exact (MulAut.conj σ).injective (hΦ₀ hMN)
  have hY : (sl2UpperUniSub k).map Φ₁ = (sl2UpperUniSub k').map Φ' := by
    rw [hΦ₁eq]
    exact hσ
  have hΦ₁range : Φ₁.range = Φ'.range := by
    rw [hΦ₁eq, ← MonoidHom.map_range Φ₀ (MulAut.conj σ).toMonoidHom]
    rw [MonoidHom.range_eq_top.mpr (MulAut.conj σ).surjective, Subgroup.map_top]
    exact hr
  refine ⟨u, ?_⟩
  unfold GGRootMatch
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz_mem : z ∈ (sl2UpperUniSub k).map phi := by rwa [hupper]
    obtain ⟨M, hM, hMz⟩ := Subgroup.mem_map.mp hz_mem
    obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hM
    have hz_eq : z = phi (sl2Upper t) := hMz.symm
    have hmem : Φ₁ (sl2Upper t) ∈ (sl2UpperUniSub k).map Φ₁ :=
      Subgroup.mem_map.mpr ⟨sl2Upper t, mem_sl2UpperUniSub_iff.mpr ⟨t, rfl⟩, rfl⟩
    rw [hY] at hmem
    obtain ⟨M', hM', hM'eq⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨t', rfl⟩ := mem_sl2UpperUniSub_iff.mp hM'
    refine ⟨model'.phi (sl2Upper t'), ?_, ?_⟩
    · rw [← model'.upper_eq]
      exact Subgroup.mem_map.mpr
        ⟨sl2Upper t', mem_sl2UpperUniSub_iff.mpr ⟨t', rfl⟩, rfl⟩
    · rw [hz_eq]
      change Φ' (sl2Upper t') = Φ₁ (sl2Upper t)
      exact hM'eq
  · exact torusClause_of_sl2Embedding phi hupper hdiag model' ψ ψ' u hΦ₁ hΦ' hY hΦ₁range
theorem selectedRootMatch_of_map_eq
    {D : UniversalRootDatum K} {D' : UniversalRootDatum K'}
    {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
    {gamma : Fin D.rank → ℤ} {delta : Fin D'.rank → ℤ}
    (model : SelectedSL2Model D k gamma) (model' : SelectedSL2Model D' k' delta)
    (ψ : K →* G) (ψ' : K' →* G)
    (hker : ψ.ker ≤ Subgroup.center K) (hker' : ψ'.ker ≤ Subgroup.center K')
    (u₀ : K)
    (hS : ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
      (ψ'.comp model'.phi).range) :
    ∃ u : K, GGRootMatch D D' ψ ψ' delta gamma u := by
  exact rootMatch_of_sl2Range_eq model.phi model.injective model.upper_eq model.diag_mem
    model' ψ ψ' hker hker' u₀ hS

end CFSG.StandardType.SelectedRoot
