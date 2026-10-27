module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

private theorem nsbK_zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

private def nsbK_lin {m n : ℕ} (Φ : (Fin m → ZMod 2) →+ (Fin n → ZMod 2)) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun := fun x => Φ x
  map_add' := fun x y => Φ.map_add x y
  map_smul' := fun c x => by
    rcases nsbK_zmod_two_cases c with rfl | rfl <;> simp

theorem natural_hom_injective {Γ : Type*} [Group Γ] {m n : ℕ}
    (ρ : Γ →* GL (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (σ : Γ →* GL (Fin n) (ZMod 2))
    (Φ : (Fin m → ZMod 2) →+ (Fin n → ZMod 2))
    (hΦ : ∀ γ x, Φ ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) =
        (σ γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Φ x))
    (h0 : Φ ≠ 0) : Function.Injective Φ := by
  obtain ⟨Φl, hΦl⟩ : ∃ L : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2), ∀ x, L x = Φ x :=
    ⟨nsbK_lin Φ, fun _ => rfl⟩
  have hker : LinearMap.ker Φl = ⊥ ∨ LinearMap.ker Φl = ⊤ := by
    apply invariant_subspace_gl m
    intro g w hw
    obtain ⟨γ, rfl⟩ := hρ g
    simp only [LinearMap.mem_ker, hΦl] at hw ⊢
    rw [hΦ γ w, hw, Matrix.mulVec_zero]
  rcases hker with hbot | htop
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ LinearMap.ker Φl := by
      rw [LinearMap.mem_ker, hΦl]
      exact ha
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  · exfalso
    apply h0
    apply AddMonoidHom.ext
    intro x
    have hmem : x ∈ LinearMap.ker Φl := by
      rw [htop]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, hΦl] at hmem
    simpa using hmem

theorem natural_hom_zero_or_eq {Γ : Type*} [Group Γ] {m n : ℕ} (hm : 2 ≤ m) (hn : n < 2 * m)
    (ρ : Γ →* GL (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (σ : Γ →* GL (Fin n) (ZMod 2))
    (Φ Φ' : (Fin m → ZMod 2) →+ (Fin n → ZMod 2))
    (hΦ : ∀ γ x, Φ ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) =
        (σ γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Φ x))
    (hΦ' : ∀ γ x, Φ' ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) =
        (σ γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Φ' x)) :
    Φ = 0 ∨ Φ' = 0 ∨ Φ = Φ' := by
  by_cases hΦ0 : Φ = 0
  · exact Or.inl hΦ0
  by_cases hΦ'0 : Φ' = 0
  · exact Or.inr (Or.inl hΦ'0)
  refine Or.inr (Or.inr ?_)
  have hinj' : Function.Injective Φ' := natural_hom_injective ρ hρ σ Φ' hΦ' hΦ'0
  obtain ⟨Φl, hΦl⟩ : ∃ L : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2), ∀ x, L x = Φ x :=
    ⟨nsbK_lin Φ, fun _ => rfl⟩
  obtain ⟨Φ'l, hΦ'l⟩ : ∃ L : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2), ∀ x, L x = Φ' x :=
    ⟨nsbK_lin Φ', fun _ => rfl⟩
  have hinj'l : Function.Injective Φ'l := fun a b hab => hinj' (by simpa only [hΦ'l] using hab)
  have hnotinj : ¬ Function.Injective (Φl.coprod Φ'l) := by
    intro hinjT
    have h := LinearMap.finrank_le_finrank_of_injective hinjT
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at h
    omega
  rw [injective_iff_map_eq_zero] at hnotinj
  push Not at hnotinj
  obtain ⟨⟨x, y⟩, hxy, hne⟩ := hnotinj
  have hxy' : Φl x + Φ'l y = 0 := by simpa using hxy
  have hx0 : x ≠ 0 := by
    intro hx
    apply hne
    have hy : Φ'l y = 0 := by
      rw [hx, map_zero, zero_add] at hxy'
      exact hxy'
    have hy0 : y = 0 := hinj'l (by rw [hy, map_zero])
    simp [hx, hy0]
  have hxS : x ∈ Submodule.comap Φl (LinearMap.range Φ'l) := by
    rw [Submodule.mem_comap, LinearMap.mem_range]
    exact ⟨-y, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hxy').symm⟩
  have hinv : ∀ g : GL (Fin m) (ZMod 2), ∀ w ∈ Submodule.comap Φl (LinearMap.range Φ'l),
      (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec w ∈
        Submodule.comap Φl (LinearMap.range Φ'l) := by
    intro g w hw
    obtain ⟨γ, rfl⟩ := hρ g
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hw)
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨(ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec y, ?_⟩
    simp only [hΦl, hΦ'l] at hy ⊢
    rw [hΦ' γ y, hΦ γ w, hy]
  have hS : Submodule.comap Φl (LinearMap.range Φ'l) = ⊤ := by
    rcases invariant_subspace_gl m _ hinv with hbot | htop
    · exfalso
      rw [hbot, Submodule.mem_bot] at hxS
      exact hx0 hxS
    · exact htop
  have hle : LinearMap.range Φl ≤ LinearMap.range Φ'l := LinearMap.range_le_iff_comap.mpr hS
  have hmemL : ∀ x, Φl x ∈ LinearMap.range Φ'l := fun x => hle (LinearMap.mem_range_self Φl x)
  obtain ⟨E, hE⟩ : ∃ E : (Fin m → ZMod 2) ≃ₗ[ZMod 2] ↥(LinearMap.range Φ'l),
      ∀ x, (E x : Fin n → ZMod 2) = Φ'l x :=
    ⟨LinearEquiv.ofInjective Φ'l hinj'l, fun x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ x, L x = E.symm ⟨Φl x, hmemL x⟩ :=
    ⟨E.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range Φ'l) Φl hmemL, fun x => rfl⟩
  have hlamL : ∀ x, Φ' (L x) = Φ x := by
    intro x
    have h1 : (E (L x) : Fin n → ZMod 2) = Φl x := by
      rw [hL, LinearEquiv.apply_symm_apply]
    rw [hE, hΦ'l] at h1
    rw [h1, hΦl]
  have hcomm : ∀ (γ : Γ) (x : Fin m → ZMod 2),
      L ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) =
        (ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (L x) := by
    intro γ x
    apply hinj'
    rw [hlamL, hΦ γ x, ← hlamL x, hΦ' γ (L x)]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin m) (Fin m) (ZMod 2), ∀ v, M.mulVec v = L v :=
    ⟨LinearMap.toMatrix' L, fun v => LinearMap.toMatrix'_mulVec _ v⟩
  have hMT : ∀ T : Matrix (Fin m) (Fin m) (ZMod 2),
      (∃ γ : Γ, (ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)) = T) → T * M = M * T := by
    rintro T ⟨γ, rfl⟩
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hM]
    exact (hcomm γ v).symm
  have htrans : ∀ t : Matrix.TransvectionStruct (Fin m) (ZMod 2), Commute t.toMatrix M := by
    intro t
    have hu : IsUnit (t.toMatrix).det := by
      rw [Matrix.TransvectionStruct.det]
      exact isUnit_one
    obtain ⟨γ, hγ⟩ := hρ (Matrix.GeneralLinearGroup.mk'' t.toMatrix hu)
    exact hMT t.toMatrix ⟨γ, congrArg Units.val hγ⟩
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct htrans
  have hLc : ∀ v, L v = c • v := by
    intro v
    rw [← hM v, ← hc, Matrix.scalar_apply]
    funext i
    simp [Matrix.mulVec_diagonal]
  rcases nsbK_zmod_two_cases c with rfl | rfl
  ·
    exfalso
    apply hΦ0
    apply AddMonoidHom.ext
    intro x
    have h1 := hlamL x
    rw [hLc x, zero_smul, map_zero] at h1
    simpa using h1.symm
  ·
    apply AddMonoidHom.ext
    intro x
    have h1 := hlamL x
    rw [hLc x, one_smul] at h1
    exact h1.symm

end CFSG.Quasithin.H13.Ch4.NSB
