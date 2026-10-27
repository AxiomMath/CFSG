module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Inputs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Module

section General

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem polar_apply_apply_of_isometry (Bf : LinearMap.BilinForm K E) (Qf : E → K)
    (hQadd : ∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f)
    (h : E ≃ₗ[K] E) (hh : ∀ e, Qf (h e) = Qf e) (e f : E) : Bf (h e) (h f) = Bf e f := by
  have h1 := hQadd (h e) (h f)
  rw [← map_add, hh, hh, hh, hQadd] at h1
  exact (add_left_cancel h1).symm

theorem exists_minimal_invariant_submodule [FiniteDimensional K E] (L : Subgroup (E ≃ₗ[K] E))
    (W : Submodule K E) (hW : W ≠ ⊥) (hWL : ∀ ℓ ∈ L, ∀ w ∈ W, ℓ w ∈ W) :
    ∃ Z ≤ W, Z ≠ ⊥ ∧ (∀ ℓ ∈ L, ∀ z ∈ Z, ℓ z ∈ Z) ∧
      ∀ Z' ≤ Z, (∀ ℓ ∈ L, ∀ z ∈ Z', ℓ z ∈ Z') → Z' = ⊥ ∨ Z' = Z := by
  obtain ⟨Z, ⟨hZW, hZ0, hZL⟩, hmin⟩ :=
    (InvImage.wf (fun Z : Submodule K E => finrank K Z) wellFounded_lt).has_min
      {Z | Z ≤ W ∧ Z ≠ ⊥ ∧ ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ z ∈ Z} ⟨W, le_rfl, hW, hWL⟩
  refine ⟨Z, hZW, hZ0, hZL, fun Z' hZ'Z hZ'L => ?_⟩
  by_cases h0 : Z' = ⊥
  · exact Or.inl h0
  · exact Or.inr (Submodule.eq_of_le_of_finrank_le hZ'Z
      (not_lt.mp (hmin Z' ⟨hZ'Z.trans hZW, h0, hZ'L⟩)))

theorem exists_hom_restrict_submodule (L : Subgroup (E ≃ₗ[K] E)) (Z : Submodule K E)
    (hZ : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ z ∈ Z) :
    ∃ σ : L →* (Z ≃ₗ[K] Z), ∀ (ℓ : L) (z : Z), (σ ℓ z : E) = (ℓ : E ≃ₗ[K] E) z :=
  ⟨{ toFun := fun ℓ =>
        { toFun := fun z => ⟨(ℓ : E ≃ₗ[K] E) z, hZ _ ℓ.2 _ z.2⟩
          map_add' := fun x y => Subtype.ext (map_add _ _ _)
          map_smul' := fun a x => Subtype.ext (map_smul _ _ _)
          invFun := fun z => ⟨(ℓ : E ≃ₗ[K] E).symm z, hZ _ (L.inv_mem ℓ.2) _ z.2⟩
          left_inv := fun z => Subtype.ext ((ℓ : E ≃ₗ[K] E).symm_apply_apply z)
          right_inv := fun z => Subtype.ext ((ℓ : E ≃ₗ[K] E).apply_symm_apply z) }
     map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
     map_mul' := fun _ _ => LinearEquiv.ext fun _ => Subtype.ext rfl }, fun _ _ => rfl⟩

theorem stroth34_false_of_fixed_vector [CharP K 2] (Bf : LinearMap.BilinForm K E) (Qf : E → K)
    (hQsmul : ∀ (a : K) (e : E), Qf (a • e) = a ^ 2 * Qf e)
    (hQadd : ∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f)
    (halt : ∀ e : E, Bf e e = 0) (hnd : ∀ e : E, (∀ f, Bf e f = 0) → e = 0)
    (H : Subgroup (E ≃ₗ[K] E)) (hHQ : ∀ h ∈ H, ∀ e : E, Qf (h e) = Qf e)
    (hHchar : ∀ χ : H →* Kˣ, χ = 1)
    (L : Subgroup (E ≃ₗ[K] E)) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (b : E) (hbs : Qf b = 0)
    (hspan : Submodule.span K (Set.range fun ℓ : L => (ℓ : E ≃ₗ[K] E) b) = ⊤)
    (Λ : Subgroup (E ≃ₗ[K] E)) (hΛH : Λ ≤ H) (hΛb : ∀ t ∈ Λ, t b = b)
    (hsing : ∀ v : E, (∀ t ∈ Λ, t v = v) → Qf v = 0 → ∃ s : K, v = s • b)
    (e₀ : E) (he₀ : e₀ ≠ 0) (he₀L : ∀ ℓ ∈ L, ℓ e₀ = e₀) : False := by
  have hBL : ∀ ℓ ∈ L, ∀ e f : E, Bf (ℓ e) (ℓ f) = Bf e f := fun ℓ hℓ =>
    polar_apply_apply_of_isometry Bf Qf hQadd ℓ (hHQ ℓ (hLH hℓ))
  have key : ∀ e, (∀ ℓ ∈ L, ℓ e = e) → Bf e b = 0 → e = 0 := by
    intro e he heb
    have hle : Submodule.span K (Set.range fun ℓ : L => (ℓ : E ≃ₗ[K] E) b) ≤
        LinearMap.ker (Bf e) := by
      rw [Submodule.span_le]
      rintro _ ⟨ℓ, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      calc Bf e ((ℓ : E ≃ₗ[K] E) b) = Bf ((ℓ : E ≃ₗ[K] E) e) ((ℓ : E ≃ₗ[K] E) b) := by
            rw [he ℓ ℓ.2]
        _ = 0 := (hBL ℓ ℓ.2 e b).trans heb
    rw [hspan] at hle
    exact hnd e fun f => LinearMap.mem_ker.mp (hle Submodule.mem_top)
  have hBe : Bf e₀ b ≠ 0 := fun h => he₀ (key e₀ he₀L h)
  have hHF : ∀ h ∈ H, ∀ ℓ ∈ L, ℓ (h e₀) = h e₀ := by
    intro h hh ℓ hℓ
    have hmem := hLn.conj_mem _ (Subgroup.mem_subgroupOf.mpr hℓ :
      (⟨ℓ, hLH hℓ⟩ : H) ∈ L.subgroupOf H) (⟨h, hh⟩ : H)⁻¹
    rw [Subgroup.mem_subgroupOf] at hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hmem
    have h1 := he₀L _ hmem
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv] at h1
    calc ℓ (h e₀) = h (h.symm (ℓ (h e₀))) := (h.apply_symm_apply _).symm
      _ = h e₀ := by rw [h1]
  have hmult : ∀ h : H, (h : E ≃ₗ[K] E) e₀ = (Bf ((h : E ≃ₗ[K] E) e₀) b / Bf e₀ b) • e₀ := by
    intro h
    refine sub_eq_zero.mp (key _ (fun ℓ hℓ => ?_) ?_)
    · rw [map_sub, map_smul, hHF h h.2 ℓ hℓ, he₀L ℓ hℓ]
    · rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        div_mul_cancel₀ _ hBe, sub_self]
  obtain ⟨c, hc⟩ : ∃ c : H → K, ∀ h : H, (h : E ≃ₗ[K] E) e₀ = c h • e₀ := ⟨_, hmult⟩
  have hc0 : ∀ h : H, c h ≠ 0 := by
    intro h h0
    have h1 := hc h
    rw [h0, zero_smul, LinearEquiv.map_eq_zero_iff] at h1
    exact he₀ h1
  have hcmul : ∀ h₁ h₂ : H, c (h₁ * h₂) = c h₁ * c h₂ := by
    intro h₁ h₂
    apply smul_left_injective K he₀
    dsimp only
    rw [← hc, Subgroup.coe_mul, LinearEquiv.mul_apply, hc, map_smul, hc, smul_smul, mul_comm]
  let χ : H →* Kˣ := MonoidHom.mk' (fun h => Units.mk0 (c h) (hc0 h)) fun h₁ h₂ =>
    Units.ext (by simp [hcmul])
  have hHfix : ∀ h ∈ H, h e₀ = e₀ := by
    intro h hh
    have h1 : χ ⟨h, hh⟩ = 1 := by rw [hHchar χ, MonoidHom.one_apply]
    have h2 : c ⟨h, hh⟩ = 1 := by
      have := congrArg Units.val h1
      simpa [χ] using this
    have h3 := hc ⟨h, hh⟩
    rw [h2, one_smul] at h3
    exact h3
  obtain ⟨s, hs⟩ := hsing (e₀ + (Qf e₀ / Bf e₀ b) • b)
    (fun t ht => by rw [map_add, map_smul, hHfix t (hΛH ht), hΛb t ht])
    (by
      rw [hQadd, hQsmul, hbs, mul_zero, add_zero, map_smul, smul_eq_mul,
        div_mul_cancel₀ _ hBe]
      exact CharTwo.add_self_eq_zero _)
  have he : e₀ = (s - Qf e₀ / Bf e₀ b) • b := by
    rw [sub_smul, ← hs]
    abel
  apply hBe
  rw [he, map_smul, LinearMap.smul_apply, halt, smul_zero]

end General

theorem finrank_minimal_invariant_eq_two_pow (hSL2 : SL2ModuleDimStatement) {k : ℕ}
    (hk : 2 ≤ k) {E : Type} [AddCommGroup E] [Module (GaloisField 2 k) E]
    [Module.Finite (GaloisField 2 k) E] (L : Subgroup (E ≃ₗ[GaloisField 2 k] E))
    (hLiso : Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * k))))
    (Z : Submodule (GaloisField 2 k) E) (hZ0 : Z ≠ ⊥) (hZL : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ z ∈ Z)
    (hmin : ∀ Z' ≤ Z, (∀ ℓ ∈ L, ∀ z ∈ Z', ℓ z ∈ Z') → Z' = ⊥ ∨ Z' = Z)
    (hfix : ∀ z ∈ Z, (∀ ℓ ∈ L, ℓ z = z) → z = 0) :
    ∃ j : ℕ, 2 ≤ j ∧ finrank (GaloisField 2 k) Z = 2 ^ j := by
  obtain ⟨φ⟩ := hLiso
  obtain ⟨σ, hσ⟩ := exists_hom_restrict_submodule L Z hZL
  haveI : Nontrivial Z := Submodule.nontrivial_iff_ne_bot.mpr hZ0
  have hρ : ∀ ℓ : L, (σ.comp φ.symm.toMonoidHom) (φ ℓ) = σ ℓ := fun ℓ => by simp
  refine hSL2 k hk Z (σ.comp φ.symm.toMonoidHom) (fun W hW => ?_) ?_
  · have hWL : ∀ ℓ ∈ L, ∀ x ∈ W.map Z.subtype, ℓ x ∈ W.map Z.subtype := by
      intro ℓ hℓ x hx
      obtain ⟨w, hwW, rfl⟩ := Submodule.mem_map.mp hx
      refine Submodule.mem_map.mpr ⟨σ ⟨ℓ, hℓ⟩ w, ?_, hσ _ _⟩
      rw [← hρ]
      exact hW _ w hwW
    rcases hmin _ (Submodule.map_subtype_le Z W) hWL with h | h
    · left
      apply Submodule.map_injective_of_injective Z.injective_subtype
      rw [h, Submodule.map_bot]
    · right
      apply Submodule.map_injective_of_injective Z.injective_subtype
      rw [h, Submodule.map_subtype_top]
  · by_contra hcon
    obtain ⟨z, hzZ, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ0
    refine hz0 (hfix z hzZ fun ℓ hℓ => ?_)
    have h2 : σ ⟨ℓ, hℓ⟩ = 1 := by
      rw [← hρ]
      exact not_not.mp fun h => hcon ⟨_, h⟩
    have h3 := hσ ⟨ℓ, hℓ⟩ ⟨z, hzZ⟩
    rw [h2] at h3
    exact h3.symm

theorem exists_fixed_vector_of_sl2 (hSL2 : SL2ModuleDimStatement) {k : ℕ} (hk : 2 ≤ k)
    (E : Type) [AddCommGroup E] [Module (GaloisField 2 k) E] [Module.Finite (GaloisField 2 k) E]
    (hdim : finrank (GaloisField 2 k) E = 6)
    (Bf : LinearMap.BilinForm (GaloisField 2 k) E)
    (halt : ∀ e : E, Bf e e = 0) (hnd : ∀ e : E, (∀ f, Bf e f = 0) → e = 0)
    (L : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hBL : ∀ ℓ ∈ L, ∀ e f, Bf (ℓ e) (ℓ f) = Bf e f)
    (hLiso : Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * k)))) :
    ∃ e : E, e ≠ 0 ∧ ∀ ℓ ∈ L, ℓ e = e := by
  by_contra hF
  have hfix : ∀ e : E, (∀ ℓ ∈ L, ℓ e = e) → e = 0 := fun e he => by
    by_contra h0
    exact hF ⟨e, h0, he⟩
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨X, -, hX0, hXL, hXmin⟩ :=
    exists_minimal_invariant_submodule L ⊤ top_ne_bot fun _ _ _ _ => Submodule.mem_top
  obtain ⟨j, hj, hXj⟩ :=
    finrank_minimal_invariant_eq_two_pow hSL2 hk L hLiso X hX0 hXL hXmin fun z _ => hfix z
  have hX4 : finrank (GaloisField 2 k) X = 4 := by
    have h6 : finrank (GaloisField 2 k) X ≤ 6 := hdim ▸ Submodule.finrank_le X
    rw [hXj] at h6 ⊢
    have hj3 : j < 3 := by
      by_contra hj3
      have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj3)
      omega
    interval_cases j
    rfl
  have hBnd : Bf.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (LinearMap.IsAlt.isRefl halt)).mpr hnd
  have hXp : finrank (GaloisField 2 k) (Bf.orthogonal X) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hBnd, hdim, hX4]
  have hXpL : ∀ ℓ ∈ L, ∀ m ∈ Bf.orthogonal X, ℓ m ∈ Bf.orthogonal X := by
    intro ℓ hℓ m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm ⊢
    intro n hn
    have h1 := hm _ (hXL ℓ⁻¹ (L.inv_mem hℓ) n hn)
    rw [← hBL ℓ hℓ, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h1
    exact h1
  have hXp0 : Bf.orthogonal X ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hXp
    omega
  obtain ⟨Z, hZXp, hZ0, hZL, hZmin⟩ := exists_minimal_invariant_submodule L _ hXp0 hXpL
  obtain ⟨j', hj', hZj⟩ :=
    finrank_minimal_invariant_eq_two_pow hSL2 hk L hLiso Z hZ0 hZL hZmin fun z _ => hfix z
  have h1 := Submodule.finrank_mono hZXp
  rw [hZj, hXp] at h1
  have : 2 ^ 2 ≤ 2 ^ j' := Nat.pow_le_pow_right (by norm_num) hj'
  omega

theorem stroth34_module_false (hSL2 : SL2ModuleDimStatement) {k : ℕ} (hk : 2 ≤ k)
    (E : Type) [AddCommGroup E] [Module (GaloisField 2 k) E] [Module.Finite (GaloisField 2 k) E]
    (hdim : Module.finrank (GaloisField 2 k) E = 6)
    (Bf : LinearMap.BilinForm (GaloisField 2 k) E) (Qf : E → GaloisField 2 k)
    (hQsmul : ∀ (a : GaloisField 2 k) (e : E), Qf (a • e) = a ^ 2 * Qf e)
    (hQadd : ∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f)
    (halt : ∀ e : E, Bf e e = 0) (hnd : ∀ e : E, (∀ f, Bf e f = 0) → e = 0)
    (H : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hHQ : ∀ h ∈ H, ∀ e : E, Qf (h e) = Qf e)
    (hHchar : ∀ χ : H →* (GaloisField 2 k)ˣ, χ = 1)
    (L : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hLsimple : IsSimpleGroup L)
    (hLiso : Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * k))))
    (b : E) (hb0 : b ≠ 0) (hbs : Qf b = 0)
    (hspan : Submodule.span (GaloisField 2 k)
      (Set.range fun ℓ : L => ((ℓ : E ≃ₗ[GaloisField 2 k] E)) b) = ⊤)
    (Λ : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hΛH : Λ ≤ H) (hΛb : ∀ t ∈ Λ, t b = b)
    (hsing : ∀ v : E, (∀ t ∈ Λ, t v = v) → Qf v = 0 → ∃ s : GaloisField 2 k, v = s • b) :
    False := by
  obtain ⟨e₀, he₀, he₀L⟩ := exists_fixed_vector_of_sl2 hSL2 hk E hdim Bf halt hnd L
    (fun ℓ hℓ => polar_apply_apply_of_isometry Bf Qf hQadd ℓ (hHQ ℓ (hLH hℓ))) hLiso
  exact stroth34_false_of_fixed_vector Bf Qf hQsmul hQadd halt hnd H hHQ hHchar L hLH hLn b hbs
    hspan Λ hΛH hΛb hsing e₀ he₀ he₀L

end CFSG.RankThree.GF2n.Stroth80
