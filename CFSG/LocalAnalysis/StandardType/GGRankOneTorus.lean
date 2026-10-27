module

public import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerBorel

public section

namespace CFSG.StandardType.RankOneXfer

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.StandardType.PsiDiag
  CFSG.StandardType.PsiDiagChar

section Elements

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K}

private theorem scalarSub_le_normalizer
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    scalarSub x γ ≤ Subgroup.normalizer (D.rootGroup γ : Set K) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨χ, hχ⟩ := mem_scalarSub_iff.mp ht
    obtain ⟨c, hc⟩ := ((hE.param γ hγ).1 z).mp hz
    rw [← hc, hχ c]
    exact ((hE.param γ hγ).1 _).mpr ⟨χ * c, rfl⟩
  · intro hz
    obtain ⟨χ, hχ⟩ := mem_scalarSub_iff.mp ht
    obtain ⟨χ', hχ'⟩ := mem_scalarSub_iff.mp ((scalarSub x γ).inv_mem ht)
    obtain ⟨c, hc⟩ := ((hE.param γ hγ).1 _).mp hz
    have hχ'' : t⁻¹ * x γ c * t = x γ ((χ' : k) * c) := by
      simpa only [inv_inv] using hχ' c
    have hz_eq : z = t⁻¹ * (t * z * t⁻¹) * t := by group
    rw [hz_eq, ← hc, hχ'']
    exact ((hE.param γ hγ).1 _).mpr ⟨χ' * c, rfl⟩

theorem torusElt_eq_map_sl2Diag (i : Fin D.rank)
    (φ : Matrix.SpecialLinearGroup (Fin 2) k →* K)
    (hu : ∀ c, φ (sl2Upper c) = x (Pi.single i 1) c)
    (hl : ∀ c, φ (sl2Lower c) = x (-Pi.single i 1) c) (t : kˣ) :
    torusElt x i t = φ (sl2Diag t) := by
  unfold torusElt weylElement
  simp only [inv_one, Units.val_one, Units.val_neg]
  rw [← hu t, ← hl (-(t⁻¹ : kˣ)), ← hu 1, ← hl (-(1 : k))]
  simpa only [map_mul, map_inv] using congrArg φ (sl2_weyl_mul_inv t)

theorem map_sl2Diag_mem_ggTorus
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (i : Fin D.rank)
    (φ : Matrix.SpecialLinearGroup (Fin 2) k →* K)
    (hu : ∀ c, φ (sl2Upper c) = x (Pi.single i 1) c)
    (hl : ∀ c, φ (sl2Lower c) = x (-Pi.single i 1) c) (t : kˣ) :
    φ (sl2Diag t) ∈ ggTorus D := by
  rw [← torusElt_eq_map_sl2Diag i φ hu hl t]
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  exact scalarSub_le_normalizer hE hγ (torusElt_mem_scalarSub hE i t hγ)

end Elements

section Clause

variable {K K' G : Type*} [Group K] [Group K'] [Group G]
  {D : UniversalRootDatum K} {D' : UniversalRootDatum K'}
  {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
  {x : (Fin D.rank → ℤ) → k → K} {x' : (Fin D'.rank → ℤ) → k' → K'}

theorem rootMatch_torus_clause
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    {C' : (Fin D'.rank → ℤ) → (Fin D'.rank → ℤ) → ℕ × ℕ → ℤ}
    {O' : CommOrder (RootSystem.ofCartan D'.isFiniteType D'.divisible)}
    (hE : ChevalleyExtras D k x C O) (hE' : ChevalleyExtras D' k' x' C' O')
    (hlin : ∀ h' ∈ ggTorus D', ∀ i' : Fin D'.rank, ∃ χ : k', ∀ c : k',
      h' * x' (Pi.single i' 1) c * h'⁻¹ = x' (Pi.single i' 1) (χ * c))
    (ψ : K →* G) (ψ' : K' →* G) (i : Fin D.rank) (i' : Fin D'.rank) (u : K)
    (φ : Matrix.SpecialLinearGroup (Fin 2) k →* K)
    (hφu : ∀ c, φ (sl2Upper c) = x (Pi.single i 1) c)
    (hφl : ∀ c, φ (sl2Lower c) = x (-Pi.single i 1) c)
    (φ' : Matrix.SpecialLinearGroup (Fin 2) k' →* K')
    (hφ'u : ∀ c, φ' (sl2Upper c) = x' (Pi.single i' 1) c)
    (hφ'l : ∀ c, φ' (sl2Lower c) = x' (-Pi.single i' 1) c)
    (hΦ : Function.Injective ((ψ.comp (MulAut.conj u).toMonoidHom).comp φ))
    (hΦ' : Function.Injective (ψ'.comp φ'))
    (hY : (sl2UpperUniSub k).map ((ψ.comp (MulAut.conj u).toMonoidHom).comp φ) =
      (sl2UpperUniSub k').map (ψ'.comp φ'))
    (hS : ((ψ.comp (MulAut.conj u).toMonoidHom).comp φ).range = (ψ'.comp φ').range) :
    ∀ h' ∈ ggTorus D', ∃ h ∈ ggTorus D, ∀ z ∈ D.rootGroup (Pi.single i 1),
      ∀ z' ∈ D'.rootGroup (Pi.single i' 1),
        ψ' z' = ψ (u * z * u⁻¹) → ψ' (h' * z' * h'⁻¹) = ψ (u * (h * z * h⁻¹) * u⁻¹) := by
  let Φ₁ : Matrix.SpecialLinearGroup (Fin 2) k →* G :=
    (ψ.comp (MulAut.conj u).toMonoidHom).comp φ
  let Φ' : Matrix.SpecialLinearGroup (Fin 2) k' →* G := ψ'.comp φ'
  have hΦ₁ : Function.Injective Φ₁ := hΦ
  have hY' : (sl2UpperUniSub k).map Φ₁ = (sl2UpperUniSub k').map Φ' := hY
  have hS' : Φ₁.range = Φ'.range := hS
  intro h' hh'
  obtain ⟨χ, hχ⟩ := hlin h' hh' i'
  have hχ0 : χ ≠ 0 := by
    obtain ⟨χ₂, hχ₂⟩ := hlin h'⁻¹ ((ggTorus D').inv_mem hh') i'
    have hχ₂' : ∀ c : k', h'⁻¹ * x' (Pi.single i' 1) c * h' =
        x' (Pi.single i' 1) (χ₂ * c) := by
      intro c
      simpa only [inv_inv] using hχ₂ c
    have h1 : (1 : k') = χ * χ₂ := by
      apply (hE'.param (Pi.single i' 1) (single_mem_roots i')).2.2
      calc x' (Pi.single i' 1) (1 : k')
          = h' * (h'⁻¹ * x' (Pi.single i' 1) (1 : k') * h') * h'⁻¹ := by group
        _ = h' * x' (Pi.single i' 1) (χ₂ * 1) * h'⁻¹ := by rw [hχ₂' 1]
        _ = x' (Pi.single i' 1) (χ * (χ₂ * 1)) := hχ (χ₂ * 1)
        _ = x' (Pi.single i' 1) (χ * χ₂) := by rw [mul_one]
    intro h0
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1
  let e : k'ˣ := Units.mk0 χ hχ0
  obtain ⟨ζ, hζ⟩ := exists_sq_eq e
  have hζval : ((ζ : k')) ^ 2 = χ := by
    have h := congrArg (fun s : k'ˣ => (s : k')) hζ
    simpa [e] using h
  have hd' : ∀ c : k',
      φ' (sl2Diag ζ) * x' (Pi.single i' 1) c * (φ' (sl2Diag ζ))⁻¹ =
        x' (Pi.single i' 1) (χ * c) := by
    intro c
    calc φ' (sl2Diag ζ) * x' (Pi.single i' 1) c * (φ' (sl2Diag ζ))⁻¹
        = φ' (sl2Diag ζ) * φ' (sl2Upper c) * (φ' (sl2Diag ζ))⁻¹ := by rw [hφ'u c]
      _ = φ' (sl2Diag ζ * sl2Upper c * (sl2Diag ζ)⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = φ' (sl2Upper (((ζ : k') ^ 2) * c)) := by rw [sl2Diag_conj_sl2Upper]
      _ = φ' (sl2Upper (χ * c)) := by rw [hζval]
      _ = x' (Pi.single i' 1) (χ * c) := by rw [hφ'u (χ * c)]
  have hd₁ : Φ' (sl2Diag ζ) ∈ Φ₁.range := by
    rw [hS']
    exact ⟨sl2Diag ζ, rfl⟩
  obtain ⟨τ, hτ⟩ := hd₁
  have hconj_exists : ∀ c : k, ∃ c' : k, τ * sl2Upper c * τ⁻¹ = sl2Upper c' := by
    intro c
    have hmem : Φ₁ (sl2Upper c) ∈ (sl2UpperUniSub k').map Φ' := by
      rw [← hY']
      exact Subgroup.mem_map.mpr ⟨sl2Upper c, mem_sl2UpperUniSub_iff.mpr ⟨c, rfl⟩, rfl⟩
    obtain ⟨M, hM, hMΦ⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨ee, rfl⟩ := mem_sl2UpperUniSub_iff.mp hM
    have hconj : Φ₁ (τ * sl2Upper c * τ⁻¹) = Φ' (sl2Upper (χ * ee)) := by
      calc Φ₁ (τ * sl2Upper c * τ⁻¹)
          = Φ₁ τ * Φ₁ (sl2Upper c) * (Φ₁ τ)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = Φ' (sl2Diag ζ) * Φ' (sl2Upper ee) * (Φ' (sl2Diag ζ))⁻¹ := by rw [hτ, ← hMΦ]
        _ = Φ' (sl2Diag ζ * sl2Upper ee * (sl2Diag ζ)⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = Φ' (sl2Upper (((ζ : k') ^ 2) * ee)) := by rw [sl2Diag_conj_sl2Upper]
        _ = Φ' (sl2Upper (χ * ee)) := by rw [hζval]
    have hmem2 : Φ' (sl2Upper (χ * ee)) ∈ (sl2UpperUniSub k).map Φ₁ := by
      rw [hY']
      exact Subgroup.mem_map.mpr
        ⟨sl2Upper (χ * ee), mem_sl2UpperUniSub_iff.mpr ⟨χ * ee, rfl⟩, rfl⟩
    obtain ⟨M', hM', hM'Φ⟩ := Subgroup.mem_map.mp hmem2
    obtain ⟨c', rfl⟩ := mem_sl2UpperUniSub_iff.mp hM'
    refine ⟨c', hΦ₁ ?_⟩
    rw [hconj, hM'Φ]
  obtain ⟨a, ha⟩ := exists_sq_conj_of_conj_upper hconj_exists
  refine ⟨φ (sl2Diag a), map_sl2Diag_mem_ggTorus hE i φ hφu hφl a, ?_⟩
  intro z hz z' hz' hzz'
  obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
  obtain ⟨c', hc'⟩ := ((hE'.param (Pi.single i' 1) (single_mem_roots i')).1 z').mp hz'
  have hz_eq : z = φ (sl2Upper c) := by rw [← hc, ← hφu c]
  have hz'_eq : z' = φ' (sl2Upper c') := by rw [← hc', ← hφ'u c']
  have hS_eq : ψ' z' = Φ₁ (sl2Upper c) := by
    rw [hzz', hz_eq]
    rfl
  have hleft : ψ' (h' * z' * h'⁻¹) = Φ₁ (sl2Upper ((a : k) ^ 2 * c)) := by
    calc ψ' (h' * z' * h'⁻¹)
        = ψ' (h' * x' (Pi.single i' 1) c' * h'⁻¹) := by rw [← hc']
      _ = ψ' (x' (Pi.single i' 1) (χ * c')) := by rw [hχ c']
      _ = ψ' (φ' (sl2Upper (χ * c'))) := by rw [← hφ'u (χ * c')]
      _ = ψ' (φ' (sl2Diag ζ * sl2Upper c' * (sl2Diag ζ)⁻¹)) := by
            rw [sl2Diag_conj_sl2Upper, hζval]
      _ = ψ' (φ' (sl2Diag ζ) * φ' (sl2Upper c') * (φ' (sl2Diag ζ))⁻¹) := by
            congr 1
            rw [map_mul, map_mul, map_inv]
      _ = ψ' (φ' (sl2Diag ζ)) * ψ' (φ' (sl2Upper c')) * (ψ' (φ' (sl2Diag ζ)))⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = Φ' (sl2Diag ζ) * ψ' z' * (Φ' (sl2Diag ζ))⁻¹ := by
            rw [← hz'_eq]
            rfl
      _ = Φ' (sl2Diag ζ) * Φ₁ (sl2Upper c) * (Φ' (sl2Diag ζ))⁻¹ := by rw [hS_eq]
      _ = Φ₁ τ * Φ₁ (sl2Upper c) * (Φ₁ τ)⁻¹ := by rw [← hτ]
      _ = Φ₁ (τ * sl2Upper c * τ⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = Φ₁ (sl2Upper ((a : k) ^ 2 * c)) := by rw [ha c]
  have hright : ψ (u * (φ (sl2Diag a) * z * (φ (sl2Diag a))⁻¹) * u⁻¹) =
      Φ₁ (sl2Upper ((a : k) ^ 2 * c)) := by
    have hz_conj : φ (sl2Diag a) * φ (sl2Upper c) * (φ (sl2Diag a))⁻¹ =
        φ (sl2Upper ((a : k) ^ 2 * c)) := by
      calc φ (sl2Diag a) * φ (sl2Upper c) * (φ (sl2Diag a))⁻¹
          = φ (sl2Diag a * sl2Upper c * (sl2Diag a)⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = φ (sl2Upper ((a : k) ^ 2 * c)) := by rw [sl2Diag_conj_sl2Upper]
    rw [hz_eq, hz_conj]
    rfl
  rw [hleft, hright]

end Clause

end CFSG.StandardType.RankOneXfer
