module

public import CFSG.Milestones.ASVolI.F429.aC2U4
public import CFSG.Milestones.ASVolI.F429.aC5U5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {E : Type} [Group E]

theorem burnsideF429a_c2ab_of_hom {S T : Subgroup E} {Q : Type*} [Group Q] (π : E →* Q)
    (hST : S ≤ T) (hker : ∀ r ∈ T, π r = 1 → r ∈ S) (hS1 : ∀ s ∈ S, π s = 1) {t₁ : E}
    (ht₁T : t₁ ∈ T) (hgen : Subgroup.zpowers (π t₁) = T.map π)
    (hord : t₁ ^ orderOf (π t₁) = 1) :
    (∃ t ∈ T, T = Subgroup.zpowers t ⊔ S) ∧ ∃ H : Subgroup E, IsComplementIn H S T := by
  have hpow : ∀ r ∈ T, ∃ n : ℤ, π t₁ ^ n = π r := fun r hr =>
    Subgroup.mem_zpowers_iff.mp (by rw [hgen]; exact ⟨r, hr, rfl⟩)
  have hsplit : ∀ r ∈ T, ∃ n : ℤ, r * t₁ ^ (-n) ∈ S ∧ r = r * t₁ ^ (-n) * t₁ ^ n := by
    intro r hr
    obtain ⟨n, hn⟩ := hpow r hr
    refine ⟨n, hker _ (T.mul_mem hr (T.zpow_mem ht₁T _)) ?_, by group⟩
    rw [map_mul, map_zpow, ← hn, ← zpow_add, add_neg_cancel, zpow_zero]
  refine ⟨⟨t₁, ht₁T, le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr ht₁T) hST)⟩,
    ⟨Subgroup.zpowers t₁, hST, Subgroup.zpowers_le.mpr ht₁T, ?_, ?_⟩⟩
  · intro r hr
    obtain ⟨n, hnS, hn⟩ := hsplit r hr
    have h := Subgroup.mul_mem_sup hnS (Subgroup.zpow_mem_zpowers t₁ n)
    rw [← hn, sup_comm] at h
    exact h
  · rw [eq_bot_iff]
    rintro x ⟨hxS, hxH⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxH
    have h1 : π t₁ ^ n = 1 := by rw [← map_zpow]; exact hS1 _ hxS
    obtain ⟨c, rfl⟩ := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [Subgroup.mem_bot, zpow_mul, zpow_natCast, hord, one_zpow]
  · intro g hg
    obtain ⟨n, hnS, hn⟩ := hsplit g hg
    exact ⟨g * t₁ ^ (-n), hnS, t₁ ^ n, Subgroup.zpow_mem_zpowers t₁ n, hn.symm⟩

end Generic

section U5Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.Sec53F.BA

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

noncomputable def burnsideF429a_U5_fp : MulAut (hypPSU hK 2 1) →* (K ≃+* K) :=
  (Phi hK).liftOfRightInverse (Function.surjInv (Phi_surjective hK))
    (Function.rightInverse_surjInv (Phi_surjective hK))
    ⟨SemidirectProduct.rightHom.comp (semilinearSimilitudes hK 2 1).subtype,
      fun x hx => (Phi_eq_one_iff.1 hx).1⟩

theorem burnsideF429a_U5_fp_Phi (x : Gam hK) :
    burnsideF429a_U5_fp hK (Phi hK x) = (x : SemiGL (HypIndex 2 1) K).right :=
  MonoidHom.liftOfRightInverse_comp_apply (f := Phi hK) (f_inv := Function.surjInv _)
    (hf := Function.rightInverse_surjInv (Phi_surjective hK))
    (g := ⟨SemidirectProduct.rightHom.comp (semilinearSimilitudes hK 2 1).subtype,
      fun x hx => (Phi_eq_one_iff.1 hx).1⟩) (x := x)

theorem burnsideF429a_U5_fp_eq_one {ρ : MulAut (hypPSU hK 2 1)}
    (hρ : burnsideF429a_U5_fp hK ρ = 1) {k : ℕ} (hk : ρ ^ 2 ^ k = 1) :
    ∃ z : hypPSU hK 2 1, ρ = MulAut.conj z := by
  obtain ⟨x, hx⟩ := Phi_surjective hK ρ
  have hr : (x : SemiGL (HypIndex 2 1) K).right = 1 := by
    rw [← burnsideF429a_U5_fp_Phi, hx]
    exact hρ
  have hD : ρ ∈ Dlin hK := (mem_Dlin_iff hx).2 hr
  obtain ⟨z, hz⟩ := Dlin_two_mem_Pi hD hk
  exact ⟨z, hz.symm⟩

theorem burnsideF429a_U5_fp_conj (z : hypPSU hK 2 1) : burnsideF429a_U5_fp hK (MulAut.conj z) = 1 := by
  obtain ⟨g, rfl⟩ := hypProj_surjective hK 2 1 z
  have : MulAut.conj (hypProj hK 2 1 g) = Phi hK (inlG g) := (Phi_inlG g).symm
  rw [this, burnsideF429a_U5_fp_Phi]
  rfl

theorem burnsideF429a_U5_decomp (α : MulAut (hypPSU hK 2 1))
    (hα : ∀ x, α x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1) :
    ∃ u ∈ hypUnitriangular hK 2 1, ∃ x : Gam hK,
      (∃ d : HypIndex 2 1 → K, (((x : SemiGL (HypIndex 2 1) K).left : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal d) ∧
      α = innM hK u * Phi hK x := by
  obtain ⟨e, he, σ, ⟨τ, rfl⟩, rfl⟩ := u5_normal_form hK α hα
  have hDn : D0 hK ≤ Subgroup.normalizer (innB hK : Set (MulAut (hypPSU hK 2 1))) :=
    (D0_le_trivSub hK).trans (trivSub_le_normalizer_innB hK)
  obtain ⟨a, ha, d, hd, rfl⟩ := burnsideF429a_exists_mul_eq_of_mem_sup hDn he
  obtain ⟨b, hb, rfl⟩ := ha
  obtain ⟨δ, rfl⟩ := hd
  obtain ⟨u', hu', t', ht', rfl⟩ := (borelBase_u5 hK).B_eq b hb
  obtain ⟨u, hu, rfl⟩ := hu'
  obtain ⟨t, ht, rfl⟩ := ht'
  refine ⟨u, hu, inlG t * dGam hK δ.1 ((mem_normOne hK).1 δ.2) * inrGam hK τ, ?_, ?_⟩
  · obtain ⟨a₀, d₀, -, -, hmat⟩ := ht
    refine ⟨fun i => torusEntries hK a₀ d₀ i * dEnt hK δ.1 i, ?_⟩
    have e1 : ((inlG t * dGam hK δ.1 ((mem_normOne hK).1 δ.2) * inrGam hK τ : Gam hK) :
        SemiGL (HypIndex 2 1) K).left = (t : GL (HypIndex 2 1) K) * dGL hK δ.1 := by
      simp only [Subgroup.coe_mul, SemidirectProduct.mul_left, inlG, dGam, inrGam,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.left_inr,
        map_one, MulAut.one_apply, mul_one]
    rw [e1, Units.val_mul, hmat, mat_dGL, diagonal_mul_diagonal]
  · rw [map_mul (Phi hK), map_mul (Phi hK), Phi_inlG, map_mul MulAut.conj]
    simp only [mul_assoc]
    rfl

theorem burnsideF429a_U5_pow_left_diag {x : Gam hK}
    (hx : ∃ d : HypIndex 2 1 → K, (((x : SemiGL (HypIndex 2 1) K).left : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal d) (n : ℕ) :
    ∃ d : HypIndex 2 1 → K, ((((x ^ n : Gam hK) : SemiGL (HypIndex 2 1) K).left :
      GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal d := by
  obtain ⟨d, hd⟩ := hx
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨dn, hdn⟩ := ih
    refine ⟨fun i => dn i * ((x ^ n : Gam hK) : SemiGL (HypIndex 2 1) K).right (d i), ?_⟩
    rw [pow_succ, Subgroup.coe_mul, SemidirectProduct.mul_left, Units.val_mul, hdn, coe_glAut,
      hd, diagonal_map (map_zero _), diagonal_mul_diagonal]

theorem burnsideF429a_U5_eq_one_of_diag {w : hypSU hK 2 1} (hw : w ∈ hypUnitriangular hK 2 1)
    {d : HypIndex 2 1 → K}
    (hd : ((w : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal d) :
    w = 1 := by
  have h1 := (mem_hypUnitriangular.mp hw).2
  have hd1 : d = 1 := by
    funext a
    have := h1 a
    rw [hd, diagonal_apply_eq] at this
    exact this
  apply Subtype.ext
  apply Units.ext
  rw [hd, hd1]
  exact diagonal_one

end U5Model

section Main

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF429a_U5_sylow_of_setup {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {K : Type} [Field K] (hK : UnitaryFieldData 2 f K) (Ψ : hypPSU hK 2 1 ≃* ↥Gp)
    (hB : (M₁ ⊓ M₂).subgroupOf Gp = (u5PtP hK ⊓ u5LnP hK).map Ψ.toMonoidHom) :
    ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
  set φ : hypPSU hK 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (u5PtP hK ⊓ u5LnP hK).map φ := burnsideF429_inf_eq_map Ψ hB
  have htop : (⊤ : Subgroup (hypPSU hK 2 1)).map φ = Gp := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Ψ y).2
    · intro hx
      exact ⟨Ψ.symm ⟨x, hx⟩, Subgroup.mem_top _, by simp [hφdef]⟩
  rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF429a_U5_pCoreOf_borel,
    ← htop]
  exact burnsideF429_isSylowOf_map φ hφ
    (u5_sylow hK : ChF.IsSylowOf 2 (hypProjUnitriangular hK 2 1) ⊤)

theorem burnsideF429a_c2ab_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    (∃ t ∈ T, T = Subgroup.zpowers t ⊔ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
      ∃ H : Subgroup E, IsComplementIn H (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, _, hK, Ψ, hB, -, -⟩ := burnsideF429a_U5_setup5 hyp
  haveI := hK.finite
  have hSG := burnsideF429a_U5_sylow_of_setup hK Ψ hB
  obtain ⟨hSB, hTinf⟩ := burnsideF429a_T_inf_Gp hSG hT
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set φ : hypPSU hK 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (u5PtP hK ⊓ u5LnP hK).map φ := burnsideF429_inf_eq_map Ψ hB
  have hS : S = (hypProjUnitriangular hK 2 1).map φ := by
    rw [hSdef, hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ,
      burnsideF429a_U5_pCoreOf_borel]
  have hmemS : ∀ y, y ∈ hypProjUnitriangular hK 2 1 ↔ φ y ∈ S := fun y => by
    rw [hS]
    exact (Subgroup.mem_map_iff_mem hφ).symm
  let act : E →* MulAut (hypPSU hK 2 1) :=
    (MulAut.congr Ψ.symm).toMonoidHom.comp (burnsideF4d_rho Gp)
  have hact : ∀ (s : E) (x : hypPSU hK 2 1), φ (act s x) = s * φ x * s⁻¹ := by
    intro s x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp s (Ψ x))) : ↥Gp) : E) = s * ((Ψ x : ↥Gp) : E) * s⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply s (Ψ x)
  have hact_phi : ∀ x, act (φ x) = MulAut.conj x := by
    intro x
    ext y
    apply hφ
    rw [hact, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hact_inner : ∀ (s : E) (g : hypPSU hK 2 1), act s = MulAut.conj g → s = φ g := by
    intro s g h
    have h1 : act s = act (φ g) := by rw [h, hact_phi]
    have h2 : burnsideF4d_rho Gp s = burnsideF4d_rho Gp (φ g) :=
      (MulAut.congr Ψ.symm).injective h1
    exact burnsideF4d_rho_injective hyp.centralizer_trivial h2
  have hrN : ∀ s ∈ M₁ ⊓ M₂, ∀ x, act s x ∈ hypProjUnitriangular hK 2 1 ↔
      x ∈ hypProjUnitriangular hK 2 1 := by
    intro s hs x
    have hN := burnsideF429a_mem_normalizer_sbar (Gp := Gp) hs
    rw [hmemS, hmemS, hact]
    exact ((Subgroup.mem_normalizer_iff.1 hN) (φ x)).symm
  set π : E →* (K ≃+* K) := (burnsideF429a_U5_fp hK).comp act with hπdef
  have hTG : ∀ t ∈ T, t ∈ Gp → t ∈ S := fun t ht htG => by
    rw [← hTinf]
    exact ⟨ht, htG⟩
  have hker : ∀ r ∈ T, π r = 1 → r ∈ S := by
    intro r hr h1
    obtain ⟨k, hk⟩ := hT.2.1 ⟨r, hr⟩
    have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hρk : act r ^ 2 ^ k = 1 := by rw [← map_pow, hrk, map_one]
    obtain ⟨z, hz⟩ := burnsideF429a_U5_fp_eq_one hK h1 hρk
    have h2 := hact_inner r z hz
    exact hTG r hr (by rw [h2]; exact (Ψ z).2)
  have hS1 : ∀ s ∈ S, π s = 1 := by
    intro s hs
    rw [hS] at hs
    obtain ⟨z, -, rfl⟩ := hs
    show burnsideF429a_U5_fp hK (act (φ z)) = 1
    rw [hact_phi]
    exact burnsideF429a_U5_fp_conj hK z
  haveI : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨σ₀, hσ₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (T.map π)).mp inferInstance
  obtain ⟨t₀, ht₀T, rfl⟩ : σ₀ ∈ T.map π := by rw [← hσ₀]; exact Subgroup.mem_zpowers _
  obtain ⟨u, hu, x, hxd, hx⟩ := burnsideF429a_U5_decomp hK (act t₀) (hrN t₀ (hT.1 ht₀T))
  set t₁ := (φ (hypProj hK 2 1 u))⁻¹ * t₀ with ht₁def
  have huS : φ (hypProj hK 2 1 u) ∈ S := (hmemS _).1 ⟨u, hu, rfl⟩
  have ht₁T : t₁ ∈ T := T.mul_mem (T.inv_mem (hSB huS)) ht₀T
  have hact₁ : act t₁ = Phi hK x := by
    rw [ht₁def, map_mul, map_inv, hact_phi, hx]
    show (MulAut.conj (hypProj hK 2 1 u))⁻¹ * (MulAut.conj (hypProj hK 2 1 u) * Phi hK x) = _
    rw [inv_mul_cancel_left]
  have hπ₁ : π t₁ = π t₀ := by
    rw [ht₁def, map_mul, map_inv, hS1 _ huS, inv_one, one_mul]
  have hπx : π t₁ = (x : SemiGL (HypIndex 2 1) K).right := by
    show burnsideF429a_U5_fp hK (act t₁) = _
    rw [hact₁, burnsideF429a_U5_fp_Phi]
  refine (burnsideF429a_c2ab_of_hom π hSB hker hS1 ht₁T (by rw [hπ₁, hσ₀]) ?_)
  set n := orderOf (π t₁) with hn
  have hxn : ((x ^ n : Gam hK) : SemiGL (HypIndex 2 1) K).right = 1 := by
    rw [Subgroup.coe_pow, SemidirectProduct.rightHom_eq_right.symm, map_pow,
      SemidirectProduct.rightHom_eq_right, ← hπx, hn, pow_orderOf_eq_one]
  have hπn : π (t₁ ^ n) = 1 := by rw [map_pow, hn, pow_orderOf_eq_one]
  have hSn := hker _ (T.pow_mem ht₁T n) hπn
  rw [hS] at hSn
  obtain ⟨z, ⟨w, hw, rfl⟩, hzw⟩ := hSn
  have hactn : Phi hK (x ^ n) = Phi hK (inlG w) := by
    rw [map_pow, ← hact₁, ← map_pow, ← hzw, hact_phi, Phi_inlG]
    rfl
  have h1 : Phi hK ((inlG w)⁻¹ * x ^ n) = 1 := by
    rw [map_mul, map_inv, hactn, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := Phi_eq_one_iff.1 h1
  obtain ⟨dn, hdn⟩ := burnsideF429a_U5_pow_left_diag hK hxd n
  have hleft : (((inlG w)⁻¹ * x ^ n : Gam hK) : SemiGL (HypIndex 2 1) K).left =
      (w : GL (HypIndex 2 1) K)⁻¹ * ((x ^ n : Gam hK) : SemiGL (HypIndex 2 1) K).left := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_left,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right]
    simp [inlG]
  rw [hleft] at hc
  have hwd : ((w : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      diagonal (fun i => dn i * ((c⁻¹ : Kˣ) : K)) := by
    have e : (w : GL (HypIndex 2 1) K) = ((x ^ n : Gam hK) : SemiGL (HypIndex 2 1) K).left *
        GeneralLinearGroup.scalar (HypIndex 2 1) c⁻¹ := by
      rw [map_inv, ← hc]
      group
    rw [e, Units.val_mul, hdn, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      diagonal_mul_diagonal]
  rw [burnsideF429a_U5_eq_one_of_diag hK hw hwd, map_one, map_one] at hzw
  exact hzw.symm

end Main

end CFSG.ASVolI
