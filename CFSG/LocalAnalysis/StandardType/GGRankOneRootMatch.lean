module

public import CFSG.LocalAnalysis.StandardType.GGHypSix
public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
public import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
public import CFSG.LocalAnalysis.StandardType.GGRankOneTorus

public section

namespace CFSG.StandardType.RankOneXfer

open CFSG.LieType.Universal CFSG.LieType.Steinberg

private lemma ker_conj_comp_le_center {K G : Type*} [Group K] [Group G]
    (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) (u : K) :
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

private lemma rankOne_eq_range {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (i : Fin D.rank)
    (φ : Matrix.SpecialLinearGroup (Fin 2) k →* K)
    (hφu : ∀ c, φ (sl2Upper c) = x (Pi.single i 1) c)
    (hφl : ∀ c, φ (sl2Lower c) = x (-Pi.single i 1) c) :
    CFSG.LieType.CurtisTits.rankOne D.rootGroup i = φ.range := by
  apply le_antisymm
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ φ.range
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, by rw [hφu c, hc]⟩
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Lower c, by rw [hφl c, hc]⟩
  · rintro y ⟨M, rfl⟩
    have hM : M ∈ Subgroup.closure
        (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
          Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) := by
      rw [closure_sl2Upper_sl2Lower_eq_top]
      exact Subgroup.mem_top M
    have hs : (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
        Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ := by
      rintro x (hx | hx)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Upper c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφu c]
        exact Subgroup.mem_sup_left
          (((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Lower c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφl c]
        exact Subgroup.mem_sup_right
          (((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
    exact Subgroup.mem_comap.mp
      (Subgroup.mem_closure.mp hM
        ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ) hs)

theorem ggRootMatch_of_rankOne_map_eq
    {K K' G : Type*} [Group K] [Group K'] [Group G]
    {D : UniversalRootDatum K} {D' : UniversalRootDatum K'}
    {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
    (hM : GGRankOneModel D k) (hM' : GGRankOneModel D' k')
    (ψ : K →* G) (ψ' : K' →* G)
    (hker : ψ.ker ≤ Subgroup.center K) (hker' : ψ'.ker ≤ Subgroup.center K')
    (i : Fin D.rank) (i' : Fin D'.rank) (u₀ : K)
    (hS : (CFSG.LieType.CurtisTits.rankOne D.rootGroup i).map
        (ψ.comp (MulAut.conj u₀).toMonoidHom) =
      (CFSG.LieType.CurtisTits.rankOne D'.rootGroup i').map ψ') :
    ∃ u : K, GGRootMatch D D' ψ ψ' (Pi.single i' 1) (Pi.single i 1) u := by
  unfold GGRankOneModel at hM hM'
  obtain ⟨x, C, O, hE, _hlin⟩ := hM
  obtain ⟨x', C', O', hE', hlin'⟩ := hM'
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  obtain ⟨φ', hφ'inj, hφ'u, hφ'l⟩ := hE'.rankOne i'
  let θ₀ : K →* G := ψ.comp (MulAut.conj u₀).toMonoidHom
  let Φ₀ : Matrix.SpecialLinearGroup (Fin 2) k →* G := θ₀.comp φ
  let Φ' : Matrix.SpecialLinearGroup (Fin 2) k' →* G := ψ'.comp φ'
  have hθker : θ₀.ker ≤ Subgroup.center K := by
    change (ψ.comp (MulAut.conj u₀).toMonoidHom).ker ≤ Subgroup.center K
    exact ker_conj_comp_le_center ψ hker u₀
  have hΦ₀ : Function.Injective Φ₀ := by
    change Function.Injective (θ₀.comp φ)
    exact PsiDiag.injective_comp_of_ker_le_center φ hφinj θ₀ hθker
  have hΦ' : Function.Injective Φ' := by
    change Function.Injective (ψ'.comp φ')
    exact PsiDiag.injective_comp_of_ker_le_center φ' hφ'inj ψ' hker'
  have hΦ₀range : Φ₀.range = (CFSG.LieType.CurtisTits.rankOne D.rootGroup i).map θ₀ := by
    change (θ₀.comp φ).range = (CFSG.LieType.CurtisTits.rankOne D.rootGroup i).map θ₀
    rw [← MonoidHom.map_range θ₀ φ, ← rankOne_eq_range hE i φ hφu hφl]
  have hΦ'range : Φ'.range = (CFSG.LieType.CurtisTits.rankOne D'.rootGroup i').map ψ' := by
    change (ψ'.comp φ').range = (CFSG.LieType.CurtisTits.rankOne D'.rootGroup i').map ψ'
    rw [← MonoidHom.map_range ψ' φ', ← rankOne_eq_range hE' i' φ' hφ'u hφ'l]
  have hr : Φ₀.range = Φ'.range := by
    rw [hΦ₀range, hΦ'range]
    simpa only [θ₀] using hS
  obtain ⟨σ, hσ⟩ := exists_conj_sl2UpperUniSub_map_eq Φ₀ Φ' hΦ₀ hΦ' hr
  let u : K := u₀ * φ σ
  let Φ₁ : Matrix.SpecialLinearGroup (Fin 2) k →* G :=
    (ψ.comp (MulAut.conj u).toMonoidHom).comp φ
  have hφconj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) k,
      φ (σ * M * σ⁻¹) = φ σ * φ M * (φ σ)⁻¹ := by
    intro M
    rw [map_mul φ, map_mul φ, map_inv φ]
  have hΦ₁eq : Φ₁ = Φ₀.comp (MulAut.conj σ).toMonoidHom := by
    ext M
    change ψ ((MulAut.conj u) (φ M)) = θ₀ (φ ((MulAut.conj σ) M))
    rw [MulAut.conj_apply, MulAut.conj_apply]
    change ψ (u * φ M * u⁻¹) = ψ (u₀ * φ (σ * M * σ⁻¹) * u₀⁻¹)
    rw [hφconj M]
    rw [show u = u₀ * φ σ from rfl]
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
  have hΦ₁_upper : ∀ c : k, Φ₁ (sl2Upper c) = ψ (u * x (Pi.single i 1) c * u⁻¹) := by
    intro c
    change ψ ((MulAut.conj u) (φ (sl2Upper c))) = ψ (u * x (Pi.single i 1) c * u⁻¹)
    rw [MulAut.conj_apply, hφu c]
  refine ⟨u, ?_⟩
  unfold GGRootMatch
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨c, rfl⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
    have hmem : Φ₁ (sl2Upper c) ∈ (sl2UpperUniSub k).map Φ₁ :=
      Subgroup.mem_map.mpr ⟨sl2Upper c, ⟨c, rfl⟩, rfl⟩
    rw [hY] at hmem
    obtain ⟨M', hM', hM'eq⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨e, rfl⟩ := (mem_sl2UpperUniSub_iff (k := k')).mp hM'
    refine ⟨x' (Pi.single i' 1) e, ?_, ?_⟩
    · exact ((hE'.param (Pi.single i' 1) (single_mem_roots i')).1 _).mpr ⟨e, rfl⟩
    · rw [← hΦ₁_upper c, ← hM'eq]
      simp only [Φ', MonoidHom.comp_apply, hφ'u e]
  · exact rootMatch_torus_clause hE hE' hlin' ψ ψ' i i' u φ hφu hφl φ' hφ'u hφ'l
      hΦ₁ hΦ' hY hΦ₁range

end CFSG.StandardType.RankOneXfer
