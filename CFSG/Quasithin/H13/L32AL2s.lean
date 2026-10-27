module

public import CFSG.Quasithin.Background.HOm4Norm
public import CFSG.Quasithin.H13.L32AL2k
public import CFSG.Quasithin.H13.L32AL2l

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

section Semilinear

variable {W' : Type} [CommGroup W'] [Finite W']

theorem card_ker_sq_of_semilinear (hV : ∀ w : W', w * w = 1) {s f : MulAut W'}
    (hs : ∀ w, s w * s (s w) * w = 1) (hf2 : f * f = 1) (hfs : f * s = s * s * f) :
    Nat.card (commHom f).ker ^ 2 = Nat.card W' := by
  set C := (commHom f).ker with hC
  have hmem : ∀ w, w ∈ C ↔ f w = w := fun w => mem_ker_commHom
  have hff : ∀ w, f (f w) = w := fun w => by rw [← MulAut.mul_apply, hf2, MulAut.one_apply]
  have hfsw : ∀ w, f (s w) = s (s (f w)) := fun w => by
    have := congrArg (fun φ : MulAut W' => φ w) hfs
    simpa [MulAut.mul_apply] using this
  apply le_antisymm
  ·
    have hinf : C ⊓ C.map s.toMonoidHom = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hw, ⟨c, hc, rfl⟩⟩
      rw [Subgroup.mem_bot]
      have hc' : f c = c := (hmem c).mp hc
      have hw' : f (s c) = s c := (hmem _).mp hw
      have h1 : s (s c) = s c := by
        have e := hfsw c
        rw [hc', hw'] at e
        exact e.symm
      have h2 : s c = c := s.injective h1
      have h3 := hs c
      rw [h2, h2, hV c, one_mul] at h3
      show s c = 1
      rw [h2, h3]
    have h1 := card_sup_of_inf_eq_bot hinf
    rw [Subgroup.card_map_of_injective s.injective] at h1
    have h2 := Subgroup.card_le_card_group (C ⊔ C.map s.toMonoidHom)
    rw [h1] at h2
    nlinarith
  ·
    let φ : W' → ↥C × ↥C := fun w =>
      (⟨w * f w, (hmem _).mpr (by rw [map_mul, hff, mul_comm])⟩,
        ⟨s w * f (s w), (hmem _).mpr (by rw [map_mul, hff, mul_comm])⟩)
    have hrec : ∀ w, ((φ w).1 : W') = w * f w ∧ ((φ w).2 : W') = s w * f (s w) :=
      fun w => ⟨rfl, rfl⟩
    have hinv : ∀ w, s (s ((φ w).1 : W')) * ((φ w).2 : W') = w⁻¹ := by
      intro w
      rw [(hrec w).1, (hrec w).2, map_mul, map_mul, hfsw]
      have h1 : s (s (f w)) * s (s (f w)) = 1 := hV _
      have h2 := hs w
      calc s (s w) * s (s (f w)) * (s w * s (s (f w)))
          = s (s w) * s w * (s (s (f w)) * s (s (f w))) := mul_mul_mul_comm _ _ _ _
        _ = w⁻¹ := by
            rw [h1, mul_one, mul_comm]
            exact eq_inv_of_mul_eq_one_left h2
    have hφ : Function.Injective φ := by
      intro w w' h
      have h1 := hinv w
      rw [h] at h1
      have h2 := hinv w'
      rw [h1] at h2
      exact inv_injective h2
    have := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_prod] at this
    nlinarith

end Semilinear

variable {G : Type} [Group G] [Finite G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable {X : TopCtx T L V K W t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

section Phi

variable {F : Type} [Field F] [Finite F] {π : TensorG2 F →* ↥(X.img (conjClosure K T))}
  {β : Hat V (A6.g1 T V) W ≃* TensorE2 F}

omit [Finite F] in
theorem IsModel.phi_pi (Y : X.IsModel π β) (γ : TensorG2 F) :
    MulAut.congr β (π γ : MulAut (Hat V (A6.g1 T V) W)) = H.Om4.lr (γ.1 : GL (Fin 2) F) γ.2 := by
  refine MulEquiv.ext fun x => ?_
  show β ((π γ : MulAut (Hat V (A6.g1 T V) W)) (β.symm x)) = _
  rw [Y.data γ (β.symm x), MulEquiv.apply_symm_apply]
  rfl

theorem IsModel.charP (Y : X.IsModel π β) : CharP F 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero Y.two

omit [Finite F] in
theorem IsModel.map_phi_img (Y : X.IsModel π β) :
    (X.img (conjClosure K T)).map (MulAut.congr β).toMonoidHom = (H.Om4.rho (K := F)).range := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨γ, hγ⟩ := Y.surj ⟨f, hf⟩
    have hf' : f = (π γ : MulAut (Hat V (A6.g1 T V) W)) := by rw [hγ]
    set g₁ : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨((γ.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), det_eq_one γ.1⟩ with hg₁
    set g₂ : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨((γ.2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), det_eq_one γ.2⟩ with hg₂
    have e₁ : Matrix.SpecialLinearGroup.toGL g₁ = (γ.1 : GL (Fin 2) F) := Units.ext rfl
    have e₂ : Matrix.SpecialLinearGroup.toGL g₂ = (γ.2 : GL (Fin 2) F) := Units.ext rfl
    refine ⟨(g₁, g₂), ?_⟩
    rw [H.Om4.rho_apply, e₁, e₂, MulEquiv.coe_toMonoidHom, hf', Y.phi_pi]
  · rintro ⟨⟨g₁, g₂⟩, rfl⟩
    have h1 : Matrix.SpecialLinearGroup.toGL g₁ ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 F :=
      (CFSG.Semidihedral.ProjectiveSL2Cover.mem_statedSL_iff_det_eq_one F 2 _).mpr g₁.2
    have h2 : Matrix.SpecialLinearGroup.toGL g₂ ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 F :=
      (CFSG.Semidihedral.ProjectiveSL2Cover.mem_statedSL_iff_det_eq_one F 2 _).mpr g₂.2
    refine ⟨(π (⟨_, h1⟩, ⟨_, h2⟩) : MulAut (Hat V (A6.g1 T V) W)), (π _).2, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, Y.phi_pi, H.Om4.rho_apply]

theorem IsModel.phi_mem_normalizer (Y : X.IsModel π β) {f : MulAut (Hat V (A6.g1 T V) W)}
    (hf : f ∈ X.img (A6.g1 T V)) :
    MulAut.congr β f ∈ Subgroup.normalizer ((H.Om4.rho (K := F)).range : Set _) := by
  have hN := X.img_g1_le_normalizer hf
  rw [← Y.map_phi_img, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨f * y * f⁻¹, (Subgroup.mem_normalizer_iff.mp hN y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  · rintro ⟨y, hy, hyx⟩
    refine ⟨f⁻¹ * y * f, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hN) y).mp hy
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hyx ⊢
      rw [hyx]
      group

end Phi

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
