module

public import CFSG.Quasithin.H13.AS91Sec4One
public import CFSG.Quasithin.H13.AS91Sec4TwoFrame
public import CFSG.Quasithin.H13.AS91Sec4TwoModel
public import CFSG.Quasithin.Vol2.Ch8Sec2KG
public import CFSG.Quasithin.Background.SmithB45M22HatHat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour
open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z}

theorem matrix_eq_of_mulVec {A B : Matrix (Fin 6) (Fin 6) FieldFour} (hAB : ∀ x, A *ᵥ x = B *ᵥ x) :
    A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hAB])

namespace Data41

variable (D : Data41 h)

@[expose] noncomputable def ψV : h.setting.Qt ≃+ V12 := D.ψ.trans frameE

@[expose] noncomputable def Φ :
    (h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) ≃* (V12 ≃ₗ[ZMod 2] V12) where
  toFun g := @addEquivToLin V12 V12 Pi.addCommGroup (Pi.Function.module _ _ _) Pi.addCommGroup
    (Pi.Function.module _ _ _) ((D.ψV.symm.trans g.toAddEquiv).trans D.ψV)
  invFun U := addEquivToLin (U := h.setting.Qt) (W := h.setting.Qt)
    ((D.ψV.trans U.toAddEquiv).trans D.ψV.symm)
  left_inv g := LinearEquiv.ext fun v => by
    change D.ψV.symm (D.ψV (g (D.ψV.symm (D.ψV v)))) = g v
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  right_inv U := LinearEquiv.ext fun v => by
    change D.ψV (D.ψV.symm (U (D.ψV (D.ψV.symm v)))) = U v
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  map_mul' g g' := LinearEquiv.ext fun v => by
    change D.ψV ((g * g') (D.ψV.symm v)) = D.ψV (g (D.ψV.symm (D.ψV (g' (D.ψV.symm v)))))
    rw [AddEquiv.symm_apply_apply]
    rfl

theorem Φ_apply (g : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) (v : V12) :
    D.Φ g v = D.ψV (g (D.ψV.symm v)) := rfl

theorem Φ_apply_ψV (g : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) (v : h.setting.Qt) :
    D.Φ g (D.ψV v) = D.ψV (g v) := by
  rw [Φ_apply, AddEquiv.symm_apply_apply]

theorem Φ_eq_frameHom {g : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt}
    {γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour}
    (hg : ∀ v, D.ψ (g v) = (γ : Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ D.ψ v) :
    D.Φ g = frameHom γ := LinearEquiv.ext fun v => by
  rw [Φ_apply, frameHom_apply]
  change frameE (D.ψ (g (D.ψ.symm (frameE.symm v)))) = _
  rw [hg, AddEquiv.apply_symm_apply]

theorem map_cMbar : (cMbar h.setting D.θ).map D.Φ.toMonoidHom = Two.gamGrp := by
  show _ = genGrp Two.gamGens
  rw [← map_hatM22Γ₀]
  ext U
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨γ, hγ, hgγ⟩ := D.ψ_acts g hg
    exact ⟨γ, hγ, (D.Φ_eq_frameHom hgγ).symm⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨g, hg, hgγ⟩ := D.ψ_onto γ hγ
    exact ⟨g, hg, D.Φ_eq_frameHom hgγ⟩

theorem Φ_mem_gamGrp {g : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt} (hg : g ∈ cMbar h.setting D.θ) :
    D.Φ g ∈ Two.gamGrp := by
  rw [← D.map_cMbar]
  exact ⟨g, hg, rfl⟩

theorem mem_cMbar_of_Φ {g : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt} (hg : D.Φ g ∈ Two.gamGrp) :
    g ∈ cMbar h.setting D.θ := by
  rw [← D.map_cMbar] at hg
  obtain ⟨g', hg', hgg'⟩ := hg
  rwa [D.Φ.injective hgg'] at hg'

theorem exists_center_matrix :
    ∃ γ ∈ hatM22Γ₀, (∀ v, D.ψ ((D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v) =
      (γ : Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ D.ψ v) ∧
      ∀ γ' ∈ hatM22Γ₀, γ * γ' = γ' * γ := by
  obtain ⟨γ, hγ, hθγ⟩ := D.ψ_acts _ (self_mem_cMbar D.θ_mem)
  refine ⟨γ, hγ, hθγ, fun γ' hγ' => ?_⟩
  obtain ⟨g', hg', hg'γ'⟩ := D.ψ_onto γ' hγ'
  obtain ⟨m, -, hmθ, rfl⟩ := mem_cMbar.mp hg'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine matrix_eq_of_mulVec fun x => ?_
  obtain ⟨v, rfl⟩ := D.ψ.surjective x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hg'γ', ← hθγ, ← hθγ, ← hg'γ']
  congr 1
  have := congrArg (fun e : h.setting.O => (e : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v) hmθ
  exact this.symm

theorem Φ_θ :
    (∀ v, D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v = theta0 v) ∨
      ∀ v, D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v = theta0 (theta0 v) := by
  obtain ⟨γ, hγ, hθγ, hcen⟩ := D.exists_center_matrix
  have hc : (⟨γ, hγ⟩ : ↥hatM22Γ₀) ∈ center ↥hatM22Γ₀ :=
    mem_center_iff.mpr fun g => Subtype.ext (hcen g g.2).symm
  rw [center_hatM22Γ₀, mem_ker_hatM22Act_iff] at hc
  have hΦ := D.Φ_eq_frameHom hθγ
  rcases hc with h1 | hZ | hZ2
  · exfalso
    apply D.θ_ne
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply D.ψ.injective
    rw [hθγ, show γ = 1 from congrArg Subtype.val h1, Units.val_one, Matrix.one_mulVec]
    rfl
  · left
    intro v
    rw [hΦ]
    refine frameHom_ω ?_ v
    have : ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) =
        (((hatM22Z : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour) :=
      congrArg (fun g : ↥hatM22Γ₀ =>
        ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) hZ
    rw [this, hatM22Z_val]
  · right
    intro v
    rw [hΦ]
    refine frameHom_ω₂ ?_ v
    have : ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) =
        (((hatM22Z ^ 2 : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour) :=
      congrArg (fun g : ↥hatM22Γ₀ =>
        ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) hZ2
    rw [this, hatM22Z_sq_val]

@[expose] noncomputable def sPrime : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt := D.Φ.symm Two.sE

theorem Φ_sPrime : D.Φ D.sPrime = Two.sE := D.Φ.apply_symm_apply _

theorem sPrime_conj_mem {l : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt}
    (hl : l ∈ cMbar h.setting D.θ) : D.sPrime * l * D.sPrime⁻¹ ∈ cMbar h.setting D.θ := by
  apply D.mem_cMbar_of_Φ
  rw [map_mul, map_mul, map_inv, Φ_sPrime]
  exact Two.sE_conj_mem (D.Φ_mem_gamGrp hl)

theorem sPrime_conj_θ :
    D.sPrime * (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) * D.sPrime⁻¹ =
      ((D.θ⁻¹ : h.setting.O) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) := by
  apply D.Φ.injective
  rw [map_mul, map_mul, map_inv, Φ_sPrime, Subgroup.coe_inv, map_inv]
  apply LinearEquiv.ext
  intro v
  have hsθ : ∀ w, Two.sE (theta0 w) = theta0 (theta0 (Two.sE w)) := Two.sE_theta0
  have h3 := theta0_theta0_theta0
  rcases D.Φ_θ with hθ | hθ
  ·
    have hinv : ∀ w, (D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt))⁻¹ w = theta0 (theta0 w) :=
      fun w => by
        change (D.Φ _).symm w = _
        rw [LinearEquiv.symm_apply_eq, hθ, h3]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv]
    change Two.sE (D.Φ _ (Two.sE.symm v)) = _
    rw [hθ, hsθ, LinearEquiv.apply_symm_apply]
  ·
    have hinv : ∀ w, (D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt))⁻¹ w = theta0 w :=
      fun w => by
        change (D.Φ _).symm w = _
        rw [LinearEquiv.symm_apply_eq, hθ, h3]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv]
    change Two.sE (D.Φ _ (Two.sE.symm v)) = _
    rw [hθ, hsθ, hsθ, LinearEquiv.apply_symm_apply, h3]

theorem conj_θ_of_not_comm {m : h.setting.O} (hm : m ∈ h.setting.Mbar)
    (hmθ : m * D.θ ≠ D.θ * m) : m * D.θ * m⁻¹ = D.θ⁻¹ := by
  obtain ⟨k, hk⟩ := D.θ_normal m hm
  have hk' : D.θ ^ (k % 3) = m * D.θ * m⁻¹ := by
    have h1 : D.θ ^ k = m * D.θ * m⁻¹ := hk
    have h2 : D.θ ^ (k % ((orderOf D.θ : ℕ) : ℤ)) = D.θ ^ k := zpow_mod_orderOf D.θ k
    rw [D.orderOf_θ] at h2
    rw [← h1, ← h2]
    simp
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · exfalso
    rw [hr, zpow_zero] at hk'
    apply D.θ_ne
    have e : D.θ = m⁻¹ * (m * D.θ * m⁻¹) * m := by group
    rw [e, ← hk']
    group
  · exfalso
    rw [hr, zpow_one] at hk'
    apply hmθ
    calc m * D.θ = m * D.θ * m⁻¹ * m := by group
      _ = D.θ * m := by rw [← hk']
  · rw [← hk', hr, zpow_two]
    have : D.θ * D.θ * D.θ = 1 := by rw [← pow_three']; exact D.θ_pow
    exact eq_inv_of_mul_eq_one_left this

theorem conj_mem_cMbar {m : h.setting.O} (hm : m ∈ h.setting.Mbar)
    {l : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt} (hl : l ∈ cMbar h.setting D.θ) :
    (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) * l * (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)⁻¹ ∈
      cMbar h.setting D.θ := by
  obtain ⟨l', hl'M, hl'θ, rfl⟩ := mem_cMbar.mp hl
  refine mem_cMbar.mpr ⟨m * l' * m⁻¹, mul_mem (mul_mem hm hl'M) (inv_mem hm), ?_, by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]⟩
  have hc : Commute (m * l' * m⁻¹) (m * D.θ * m⁻¹) := (Commute.conj_iff m).mpr hl'θ
  by_cases hmθ : m * D.θ = D.θ * m
  · rw [show m * D.θ * m⁻¹ = D.θ by rw [hmθ]; group] at hc
    exact hc
  · rw [D.conj_θ_of_not_comm hm hmθ] at hc
    exact (Commute.inv_right_iff.mp hc)

theorem isQuasisimple_open_of {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨(Group.isPerfect_def (G := Q)).1 hq.1, hq.2.1⟩

@[expose] noncomputable def conjAut {K : Subgroup (h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)}
    (x : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) (hx : x ∈ normalizer (K : Set _)) : MulAut ↥K :=
  ((MulAut.conj x).subgroupMap K).trans
    (MulEquiv.subgroupCongr (mem_normalizer_iff_map_conj_eq.mp hx))

theorem conjAut_apply {K : Subgroup (h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)}
    (x : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) (hx : x ∈ normalizer (K : Set _)) (k : ↥K) :
    ((conjAut x hx k : ↥K) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) = x * k * x⁻¹ := rfl

theorem sPrime_mem
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    D.sPrime ∈ h.setting.Mbar.map h.setting.O.subtype := by
  classical
  haveI : Finite (h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) :=
    Finite.of_injective (fun e : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt => (e : _ → _))
      DFunLike.coe_injective
  obtain ⟨τ, hτM, hτθ⟩ := D.outer
  obtain ⟨T, hT⟩ : ∃ T : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt, T = τ := ⟨_, rfl⟩
  obtain ⟨θG, hθG⟩ : ∃ θG : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt, θG = D.θ := ⟨_, rfl⟩
  have hTθ : T * θG * T⁻¹ = θG⁻¹ := by
    have := congrArg Subtype.val (D.conj_θ_of_not_comm hτM hτθ)
    rw [hT, hθG]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hSθ : D.sPrime * θG * D.sPrime⁻¹ = θG⁻¹ := by
    rw [hθG, D.sPrime_conj_θ, Subgroup.coe_inv]
  obtain ⟨x, hx⟩ : ∃ x : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt, x = T⁻¹ * D.sPrime := ⟨_, rfl⟩
  have hxN : x ∈ normalizer (cMbar h.setting D.θ : Set (h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)) := by
    refine mem_normalizer_fintype fun l hl => ?_
    have h2 := D.conj_mem_cMbar (inv_mem hτM) (D.sPrime_conj_mem hl)
    rw [Subgroup.coe_inv, ← hT, inv_inv] at h2
    have e : x * l * x⁻¹ = T⁻¹ * (D.sPrime * l * D.sPrime⁻¹) * T := by
      rw [hx]
      group
    rw [e]
    exact h2
  have hxθ : x * θG * x⁻¹ = θG := by
    have e1 : T⁻¹ * θG⁻¹ * T = θG := by
      rw [← hTθ]
      group
    calc x * θG * x⁻¹ = T⁻¹ * (D.sPrime * θG * D.sPrime⁻¹) * T := by rw [hx]; group
      _ = θG := by rw [hSθ, e1]
  have hLq := D.hat
  obtain ⟨α, hα⟩ : ∃ α : MulAut ↥(cMbar h.setting D.θ), α = conjAut x hxN := ⟨_, rfl⟩
  obtain ⟨θL, hθL⟩ : ∃ θL : ↥(cMbar h.setting D.θ), (θL : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) =
      θG := ⟨⟨D.θ, self_mem_cMbar D.θ_mem⟩, hθG.symm⟩
  have hθLc : θL ∈ center ↥(cMbar h.setting D.θ) := by
    have : θL = ⟨D.θ, self_mem_cMbar D.θ_mem⟩ := Subtype.ext (by rw [hθL, hθG])
    rw [this]
    exact self_mem_center_cMbar D.θ_mem
  have hαθ : α θL = θL := Subtype.ext (by rw [hα, conjAut_apply, hθL]; exact hxθ)
  have hθL3 : θL ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, hθL, hθG, ← Subgroup.coe_pow, D.θ_pow,
      Subgroup.coe_one])
  have hθL1 : θL ≠ 1 := fun h1 => D.θ_ne (Subtype.ext (by
    have := congrArg Subtype.val h1
    rw [hθL, hθG] at this
    exact this))
  have hθLinv : θL ≠ θL⁻¹ := by
    intro he
    apply hθL1
    have h2 : θL * θL = 1 := by nth_rw 2 [he]; exact mul_inv_cancel θL
    calc θL = θL ^ 3 * (θL * θL)⁻¹ := by group
      _ = 1 := by rw [hθL3, h2]; group
  obtain ⟨k, hk⟩ : ∃ k : ↥(cMbar h.setting D.θ), α = MulAut.conj k := by
    by_contra hall
    push Not at hall
    have := hOut ↥(cMbar h.setting D.θ) (isQuasisimple_open_of hLq.1) hLq.2.1 hLq.2.2 α hall θL
      hθLc
    rw [hαθ] at this
    exact hθLinv this
  obtain ⟨y, hy⟩ : ∃ y : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt,
      y = (k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)⁻¹ * x := ⟨_, rfl⟩
  have hcomm : ∀ l : ↥(cMbar h.setting D.θ),
      y * (l : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) = l * y := by
    intro l
    have h1 : x * (l : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) * x⁻¹ =
        (k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) * l *
          (k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)⁻¹ := by
      have := congrArg Subtype.val (DFunLike.congr_fun hk l)
      rw [hα, conjAut_apply] at this
      rw [this, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * (l : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) =
        (k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)⁻¹ * (x * l * x⁻¹) * x := by rw [hy]; group
      _ = (k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)⁻¹ *
          ((k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) * l *
            (k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)⁻¹) * x := by rw [h1]
      _ = l * y := by rw [hy]; group
  haveI : Finite h.setting.Qt := Module.finite_of_finite (ZMod 2)
  haveI : Finite (Multiplicative h.setting.Qt) := inferInstanceAs (Finite h.setting.Qt)
  have hcard : Nat.card (Multiplicative h.setting.Qt) = 2 ^ 12 := by
    haveI : Module.Finite (ZMod 2) h.setting.Qt := Module.Finite.of_finite
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, h.setting.finrank_Qt_eq_two_mul_width, h.setting_width]
  have hsq : ∀ w : Multiplicative h.setting.Qt, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    change Multiplicative.ofAdd (Multiplicative.toAdd w + Multiplicative.toAdd w) = 1
    rw [ZModModule.add_self]
    rfl
  have hρinj : Function.Injective ((toMulAutHom h.setting.Qt).comp (cMbar h.setting D.θ).subtype) :=
    toMulAutHom_injective.comp (cMbar h.setting D.θ).subtype_injective
  have hcen := hTw ↥(cMbar h.setting D.θ) (isQuasisimple_open_of hLq.1) hLq.2.1 hLq.2.2
    (Multiplicative h.setting.Qt) hcard hsq _ hρinj
  have hymem : toMulAutHom h.setting.Qt y ∈ centralizer
      (((toMulAutHom h.setting.Qt).comp (cMbar h.setting D.θ).subtype).range :
        Set (MulAut (Multiplicative h.setting.Qt))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨l, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact (hcomm l).symm
  rw [hcen] at hymem
  obtain ⟨ζ, -, hζy⟩ := hymem
  have hζx : (ζ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) = y := by
    have : toMulAutHom h.setting.Qt (ζ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) =
        toMulAutHom h.setting.Qt y := hζy
    exact toMulAutHom_injective this
  have hS : D.sPrime = T * ((k : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) * ζ) := by
    rw [hζx, hy, hx]
    group
  obtain ⟨k₀, hk₀M, -, hk₀⟩ := mem_cMbar.mp k.2
  obtain ⟨ζ₀, hζ₀M, -, hζ₀⟩ := mem_cMbar.mp ζ.2
  refine ⟨τ * (k₀ * ζ₀), mul_mem hτM (mul_mem hk₀M hζ₀M), ?_⟩
  rw [hS, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_mul, hk₀, hζ₀, hT]

theorem exists_sPrime
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    ∃ s₀ : h.setting.O, s₀ ∈ h.setting.Mbar ∧
      (s₀ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) = D.sPrime := by
  obtain ⟨s₀, hs₀, he⟩ := D.sPrime_mem hOut hTw
  exact ⟨s₀, hs₀, he⟩

theorem map_Mbar
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    (h.setting.Mbar.map h.setting.O.subtype).map D.Φ.toMonoidHom = Two.nGrp := by
  obtain ⟨s₀, hs₀M, hs₀⟩ := D.exists_sPrime hOut hTw
  have hgamN : Two.gamGrp ≤ (h.setting.Mbar.map h.setting.O.subtype).map D.Φ.toMonoidHom := by
    rw [← D.map_cMbar]
    refine map_mono fun g hg => ?_
    obtain ⟨m, hm, -, rfl⟩ := mem_cMbar.mp hg
    exact ⟨m, hm, rfl⟩
  have hsN : Two.sE ∈ (h.setting.Mbar.map h.setting.O.subtype).map D.Φ.toMonoidHom :=
    ⟨D.sPrime, ⟨s₀, hs₀M, hs₀⟩, D.Φ_sPrime⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    by_cases hmθ : m * D.θ = D.θ * m
    · exact Two.gamGrp_le_nGrp (D.Φ_mem_gamGrp (mem_cMbar.mpr ⟨m, hm, hmθ, rfl⟩))
    ·
      have h1 := D.conj_θ_of_not_comm hm hmθ
      have h2 : s₀ * D.θ * s₀⁻¹ = D.θ⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hs₀]
        exact D.sPrime_conj_θ)
      have hl : s₀⁻¹ * m * D.θ = D.θ * (s₀⁻¹ * m) := by
        have e1 : m * D.θ = D.θ⁻¹ * m := by rw [← h1]; group
        have e2 : s₀⁻¹ * D.θ⁻¹ = D.θ * s₀⁻¹ := by
          have : s₀ * D.θ * s₀⁻¹ = D.θ⁻¹ := h2
          calc s₀⁻¹ * D.θ⁻¹ = s₀⁻¹ * (s₀ * D.θ * s₀⁻¹) := by rw [this]
            _ = D.θ * s₀⁻¹ := by group
        rw [mul_assoc, e1, ← mul_assoc, e2, mul_assoc]
      have hlL : ((s₀⁻¹ * m : h.setting.O) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) ∈
          cMbar h.setting D.θ :=
        mem_cMbar.mpr ⟨s₀⁻¹ * m, mul_mem (inv_mem hs₀M) hm, hl, rfl⟩
      have e : (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) =
          D.sPrime * ((s₀⁻¹ * m : h.setting.O) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) := by
        rw [← hs₀, ← Subgroup.coe_mul, mul_inv_cancel_left]
      change D.Φ (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) ∈ Two.nGrp
      rw [e, map_mul, D.Φ_sPrime]
      exact mul_mem Two.sE_mem (Two.gamGrp_le_nGrp (D.Φ_mem_gamGrp hlL))
  · refine (Subgroup.closure_le _).2 ?_
    rintro l ⟨r, hr, hl⟩
    have hl' : ∀ {U : V12 ≃ₗ[ZMod 2] V12}, (∀ v, U v = linOfRows r v) → l = U := fun hU =>
      LinearEquiv.ext fun v => (hl v).trans (hU v).symm
    have hm1 : Two.m1Rows ∈ Two.gamGens := by simp [Two.gamGens]
    have hm2 : Two.m2Rows ∈ Two.gamGens := by simp [Two.gamGens]
    have hinv2 : invR Two.m2Rows = Two.m2InvRows := invR_eq (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    simp only [Two.nGensI, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, U, hU, hUr⟩ := rep_gen Two.gensOK_gamGens hm1
      rw [hl' hUr]; exact hgamN hU
    · obtain ⟨-, U, hU, hUr⟩ := rep_gen Two.gensOK_gamGens hm2
      rw [hl' hUr]; exact hgamN hU
    · rw [hl' Two.sE_apply]; exact hsN
    · obtain ⟨-, U, hU, hUr⟩ := rep_gen Two.gensOK_gamGens hm1
      rw [hl' hUr]; exact hgamN hU
    · obtain ⟨-, U, hU, hUr⟩ := Two.rep_invR Two.gensOK_gamGens hm2
      rw [hinv2] at hUr
      rw [hl' hUr]; exact hgamN hU
    · rw [hl' Two.sE_inv_apply]; exact inv_mem hsN

end Data41

end CFSG.Quasithin.H13.AS91
