module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Swap16Normal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.OrbitTwo
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.GroupTheory.AlternatingFive.CommutingPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

open CFSG.QuasithinUnique.A5.Delta5 (pact isEven pact_mem pact_one mem_evenWeight_iff)

section SwapColumn

variable {W : Type} [CommGroup W] [Finite W] {L₁ L₂ : Subgroup (MulAut W)} {F : Type} [Field F]
  [Finite F] {β : W ≃* Multiplicative (Matrix (Fin 4) (Fin 4) F)}
  {ρ : ↥L₁ →* Matrix.GeneralLinearGroup (Fin 4) F} {σ : ↥L₂ →* Matrix.GeneralLinearGroup (Fin 4) F}

theorem exists_perm_column_of_congr_form (hM : IsMatModel L₁ L₂ β ρ σ)
    (hO : AlternatingNatural L₁ (matColSub β 0) ⊥ 5) :
    ∃ (ε : ↥(matColSub β 0) ≃* ↥(G6.coreMod 5))
      (φ : ↥L₁ ≃* ↥(alternatingGroup (Fin 5))),
      ∀ (a : ↥(Subgroup.normalizer (L₁ : Set (MulAut W))))
        (B : Matrix (Fin 4) (Fin 4) F),
        (∀ v, Multiplicative.toAdd (β ((a : MulAut W) v)) =
          B * Multiplicative.toAdd (β v) * Bᵀ) →
        ∀ u u' : ↥(matColSub β 0),
          Multiplicative.toAdd (β u') = B * Multiplicative.toAdd (β u) →
            ε u' = G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a) (ε u) := by
  classical
  have hL₁ne : L₁ ≠ ⊥ := by
    intro hbot
    have hsub : ∀ g : ↥L₁, ρ g = 1 := by
      intro g
      haveI : Subsingleton ↥L₁ := by rw [hbot]; infer_instance
      have hg1 : g = 1 := Subsingleton.elim g 1
      rw [hg1, map_one]
    let W₀ : AddSubgroup (Fin 4 → F) :=
      { carrier := {x | x 0 = 0}
        zero_mem' := rfl
        add_mem' := fun {x y} hx hy => by
          change x 0 = 0 at hx
          change y 0 = 0 at hy
          show (x + y) 0 = 0
          rw [Pi.add_apply, hx, hy, add_zero]
        neg_mem' := fun {x} hx => by
          change x 0 = 0 at hx
          show (-x) 0 = 0
          rw [Pi.neg_apply, hx, neg_zero] }
    have hstab : ∀ (g : ↥L₁), ∀ w ∈ W₀,
        ((((ρ g : Matrix.GeneralLinearGroup (Fin 4) F)) :
          Matrix (Fin 4) (Fin 4) F)).mulVec w ∈ W₀ := by
      intro g w hw
      rw [hsub g]
      simpa using hw
    have he₁mem : (Pi.single (1 : Fin 4) (1 : F)) ∈ W₀ := by
      show (Pi.single (1 : Fin 4) (1 : F) : Fin 4 → F) 0 = 0
      simp
    have he₁ne : (Pi.single (1 : Fin 4) (1 : F) : Fin 4 → F) ≠ 0 := by
      intro h
      have h1 : (Pi.single (1 : Fin 4) (1 : F) : Fin 4 → F) 1 = (0 : Fin 4 → F) 1 := by
        rw [h]
      simpa using h1
    have he₀not : (Pi.single (0 : Fin 4) (1 : F)) ∉ W₀ := by
      show (Pi.single (0 : Fin 4) (1 : F) : Fin 4 → F) 0 ≠ 0
      simp
    rcases hM.I_irr W₀ hstab with h | h
    · rw [h] at he₁mem
      exact he₁ne (AddSubgroup.mem_bot.mp he₁mem)
    · exact he₀not (by rw [h]; exact AddSubgroup.mem_top _)
  obtain ⟨π, ε, hπsurj, hHU, hεπ⟩ := s15_T7_exists_iso hO
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (α := Fin 5) (by norm_num)
  have hπker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      apply hL₁ne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨γ, hγ⟩ := hπsurj ⟨x, hx⟩
      have h2 : π γ = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top γ
      have h1 : (⟨x, hx⟩ : ↥L₁) = 1 := by rw [← hγ]; exact h2
      exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val h1)
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hπker
  let e : ↥(alternatingGroup (Fin 5)) ≃* ↥L₁ :=
    MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  let φ : ↥L₁ ≃* ↥(alternatingGroup (Fin 5)) := e.symm
  refine ⟨ε, φ, ?_⟩
  intro a B hB u u' hcol
  have hmem : ∀ l : ↥L₁, (a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹ ∈ L₁ :=
    fun l => (Subgroup.mem_normalizer_iff.mp a.2 l).mp l.2
  have hBunit : IsUnit B := by
    have hex : ∃ M : Matrix (Fin 4) (Fin 4) F, B * M * Bᵀ = 1 := by
      refine ⟨Multiplicative.toAdd (β ((a : MulAut W)⁻¹
        (β.symm (Multiplicative.ofAdd (1 : Matrix (Fin 4) (Fin 4) F))))), ?_⟩
      have h := hB ((a : MulAut W)⁻¹
        (β.symm (Multiplicative.ofAdd (1 : Matrix (Fin 4) (Fin 4) F))))
      have h1 : (a : MulAut W) ((a : MulAut W)⁻¹
          (β.symm (Multiplicative.ofAdd (1 : Matrix (Fin 4) (Fin 4) F)))) =
          β.symm (Multiplicative.ofAdd (1 : Matrix (Fin 4) (Fin 4) F)) := by
        rw [← MulAut.mul_apply W, mul_inv_cancel, MulAut.one_apply]
      have h2 : Multiplicative.toAdd (β (β.symm
          (Multiplicative.ofAdd (1 : Matrix (Fin 4) (Fin 4) F)))) = 1 := by simp
      rw [h1, h2] at h
      exact h.symm
    obtain ⟨M, hM1⟩ := hex
    rw [Matrix.mul_assoc] at hM1
    exact CFSG.Quasithin.SwapModel.isUnit_left_of_mul_eq_one hM1
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hBmul : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBdet
  have hB'B : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBdet
  have hBinvT : (B⁻¹)ᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBmul, Matrix.transpose_one]
  have hBTinv : Bᵀ * (B⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hB'B, Matrix.transpose_one]
  have hρconj : ∀ l : ↥L₁,
      ((ρ ⟨(a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹, hmem l⟩ :
          Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) * B⁻¹ := by
    intro l
    have hcomp : ∀ v : W,
        Multiplicative.toAdd (β (((a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹) v)) =
          B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) * B⁻¹ * Multiplicative.toAdd (β v) := by
      intro v
      have hconv : ((a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹) v =
          (a : MulAut W) ((l : MulAut W) ((a : MulAut W)⁻¹ v)) := by
        simp [MulAut.mul_apply]
      rw [hconv]
      have h1 : Multiplicative.toAdd (β ((a : MulAut W)
          ((l : MulAut W) ((a : MulAut W)⁻¹ v)))) =
          B * Multiplicative.toAdd (β ((l : MulAut W) ((a : MulAut W)⁻¹ v))) * Bᵀ := by
        simpa using hB ((l : MulAut W) ((a : MulAut W)⁻¹ v))
      have h2 : Multiplicative.toAdd (β ((l : MulAut W) ((a : MulAut W)⁻¹ v))) =
          ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            Multiplicative.toAdd (β ((a : MulAut W)⁻¹ v)) := by
        simpa using congrArg Multiplicative.toAdd (hM.hρ l ((a : MulAut W)⁻¹ v))
      have h3 : Multiplicative.toAdd (β ((a : MulAut W)⁻¹ v)) =
          B⁻¹ * Multiplicative.toAdd (β v) * (B⁻¹)ᵀ := by
        have h := hB ((a : MulAut W)⁻¹ v)
        have hAA : (a : MulAut W) ((a : MulAut W)⁻¹ v) = v := by
          rw [← MulAut.mul_apply W, mul_inv_cancel, MulAut.one_apply]
        rw [hAA] at h
        calc Multiplicative.toAdd (β ((a : MulAut W)⁻¹ v))
            = (B⁻¹ * B) * Multiplicative.toAdd (β ((a : MulAut W)⁻¹ v)) *
                (Bᵀ * (B⁻¹)ᵀ) := by rw [hB'B, hBTinv, Matrix.one_mul, Matrix.mul_one]
          _ = B⁻¹ * (B * Multiplicative.toAdd (β ((a : MulAut W)⁻¹ v)) * Bᵀ) *
                (B⁻¹)ᵀ := by noncomm_ring
          _ = B⁻¹ * Multiplicative.toAdd (β v) * (B⁻¹)ᵀ := by rw [h]
      calc Multiplicative.toAdd (β ((a : MulAut W)
              ((l : MulAut W) ((a : MulAut W)⁻¹ v))))
          = B * (((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
                Matrix (Fin 4) (Fin 4) F) *
                Multiplicative.toAdd (β ((a : MulAut W)⁻¹ v))) * Bᵀ := by rw [h1, h2]
        _ = B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) *
              Multiplicative.toAdd (β ((a : MulAut W)⁻¹ v)) * Bᵀ := by noncomm_ring
        _ = B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) * B⁻¹ * Multiplicative.toAdd (β v) := by
            rw [h3]
            calc B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
                    Matrix (Fin 4) (Fin 4) F) *
                    (B⁻¹ * Multiplicative.toAdd (β v) * (B⁻¹)ᵀ) * Bᵀ
                = B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
                    Matrix (Fin 4) (Fin 4) F) * B⁻¹ * Multiplicative.toAdd (β v) *
                    ((B⁻¹)ᵀ * Bᵀ) := by noncomm_ring
              _ = B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
                    Matrix (Fin 4) (Fin 4) F) * B⁻¹ * Multiplicative.toAdd (β v) := by
                  rw [hBinvT, Matrix.mul_one]
    have hv : Multiplicative.toAdd (β (β.symm (Multiplicative.ofAdd
        (1 : Matrix (Fin 4) (Fin 4) F)))) = 1 := by simp
    have h1 := hcomp (β.symm (Multiplicative.ofAdd (1 : Matrix (Fin 4) (Fin 4) F)))
    rw [hv, Matrix.mul_one] at h1
    have h2 := congrArg Multiplicative.toAdd (hM.hρ
      ⟨(a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹, hmem l⟩
      (β.symm (Multiplicative.ofAdd (1 : Matrix (Fin 4) (Fin 4) F))))
    rw [hv, Matrix.mul_one, toAdd_ofAdd] at h2
    rw [← h2]
    exact h1
  have hsupp : ∀ C M : Matrix (Fin 4) (Fin 4) F, (∀ i k, k ≠ 0 → M i k = 0) →
      ∀ i k, k ≠ 0 → (C * M) i k = 0 := by
    intro C M hM' i k hk
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [hM' j k hk, mul_zero]
  let F₁ : ↥(matColSub β 0) → ↥(matColSub β 0) := fun x =>
    ⟨β.symm (Multiplicative.ofAdd (B * Multiplicative.toAdd (β (x : W)))), by
      intro i k hk
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact hsupp B _ x.2 i k hk⟩
  let F₂ : ↥(matColSub β 0) → ↥(matColSub β 0) := fun x =>
    ⟨β.symm (Multiplicative.ofAdd (B⁻¹ * Multiplicative.toAdd (β (x : W)))), by
      intro i k hk
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact hsupp B⁻¹ _ x.2 i k hk⟩
  have hF₁F₂ : ∀ x, F₁ (F₂ x) = x := by
    intro x
    apply Subtype.ext
    apply β.injective
    apply Multiplicative.toAdd.injective
    dsimp only [F₁, F₂]
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rw [← Matrix.mul_assoc, hBmul, Matrix.one_mul]
  have hF₂F₁ : ∀ x, F₂ (F₁ x) = x := by
    intro x
    apply Subtype.ext
    apply β.injective
    apply Multiplicative.toAdd.injective
    dsimp only [F₁, F₂]
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rw [← Matrix.mul_assoc, hB'B, Matrix.one_mul]
  let T : ↥(matColSub β 0) ≃* ↥(matColSub β 0) :=
    { toFun := F₁
      invFun := F₂
      left_inv := hF₂F₁
      right_inv := hF₁F₂
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply β.injective
        apply Multiplicative.toAdd.injective
        have hx : Multiplicative.toAdd (β (F₁ x : W)) =
            B * Multiplicative.toAdd (β (x : W)) := by
          dsimp only [F₁]
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        have hy : Multiplicative.toAdd (β (F₁ y : W)) =
            B * Multiplicative.toAdd (β (y : W)) := by
          dsimp only [F₁]
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        have hxy : Multiplicative.toAdd (β (F₁ (x * y) : W)) =
            B * (Multiplicative.toAdd (β (x : W)) +
              Multiplicative.toAdd (β (y : W))) := by
          dsimp only [F₁]
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
          show B * Multiplicative.toAdd (β ((x : W) * (y : W))) = _
          rw [map_mul, toAdd_mul]
        have hxy' : Multiplicative.toAdd (β (F₁ x * F₁ y : W)) =
            B * Multiplicative.toAdd (β (x : W)) +
              B * Multiplicative.toAdd (β (y : W)) := by
          show Multiplicative.toAdd (β ((F₁ x : W) * (F₁ y : W))) = _
          rw [map_mul, toAdd_mul, hx, hy]
        rw [hxy]
        change B * (Multiplicative.toAdd (β (x : W)) +
            Multiplicative.toAdd (β (y : W))) =
          Multiplicative.toAdd (β ((F₁ x : W) * (F₁ y : W)))
        rw [hxy', Matrix.mul_add] }
  have hTβ : ∀ x : ↥(matColSub β 0),
      Multiplicative.toAdd (β (T x : W)) = B * Multiplicative.toAdd (β (x : W)) := by
    intro x
    show Multiplicative.toAdd (β (F₁ x : W)) = _
    dsimp only [F₁]
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hTact : ∀ (l : ↥L₁) (x : ↥(matColSub β 0)),
      (T ⟨((l : MulAut W) (x : W)), hHU l x x.2⟩ : W) =
        ((a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹) (T x : W) := by
    intro l x
    apply β.injective
    apply Multiplicative.toAdd.injective
    have hL : Multiplicative.toAdd (β (T ⟨((l : MulAut W) (x : W)), hHU l x x.2⟩ : W)) =
        B * Multiplicative.toAdd (β ((l : MulAut W) (x : W))) := hTβ _
    have hxT : Multiplicative.toAdd (β (T x : W)) = B * Multiplicative.toAdd (β (x : W)) :=
      hTβ x
    have hl : Multiplicative.toAdd (β ((l : MulAut W) (x : W))) =
        ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          Multiplicative.toAdd (β (x : W)) := by
      simpa using congrArg Multiplicative.toAdd (hM.hρ l (x : W))
    have hR : Multiplicative.toAdd (β (((a : MulAut W) * (l : MulAut W) *
        (a : MulAut W)⁻¹) (T x : W))) =
        ((ρ ⟨(a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹, hmem l⟩ :
          Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          Multiplicative.toAdd (β (T x : W)) := by
      simpa using congrArg Multiplicative.toAdd (hM.hρ ⟨_, hmem l⟩ (T x : W))
    rw [hL, hl, hR, hxT, hρconj l]
    calc B * (((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) * Multiplicative.toAdd (β (x : W)))
        = B * (((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) * (B⁻¹ * B) *
            Multiplicative.toAdd (β (x : W))) := by rw [hB'B, Matrix.mul_one]
      _ = (B * ((ρ l : Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            B⁻¹) * (B * Multiplicative.toAdd (β (x : W))) := by noncomm_ring
  let q : MulAut ↥(G6.coreMod 5) := (ε.symm.trans T).trans ε
  have hq_apply : ∀ x : ↥(G6.coreMod 5), q x = ε (T (ε.symm x)) := fun _ => rfl
  have hsign : ∀ γ ∈ alternatingGroup (Fin 5),
      (CFSG.OddStandard.rhoOf φ a) * γ * (CFSG.OddStandard.rhoOf φ a)⁻¹ ∈
        alternatingGroup (Fin 5) := by
    intro γ hγ
    exact Subgroup.Normal.conj_mem (H := alternatingGroup (Fin 5)) inferInstance γ hγ _
  have hπφ : ∀ l : ↥L₁, ((π (φ l) : ↥L₁) : MulAut W) = (l : MulAut W) := by
    intro l
    have h := e.apply_symm_apply l
    exact congrArg Subtype.val h
  have hq_rel : ∀ γ ∈ alternatingGroup (Fin 5),
      q * G6.coreAct 5 γ = G6.coreAct 5
        (CFSG.OddStandard.rhoOf φ a * γ * (CFSG.OddStandard.rhoOf φ a)⁻¹) * q := by
    intro γ hγ
    apply MulEquiv.ext
    intro x
    let l : ↥L₁ := π ⟨γ, hγ⟩
    have hφl : φ l = ⟨γ, hγ⟩ := by
      have h := e.symm_apply_apply ⟨γ, hγ⟩
      exact h
    let u : ↥(matColSub β 0) := ε.symm x
    let lu : ↥(matColSub β 0) := ⟨(l : MulAut W) (u : W), hHU l u u.2⟩
    have hx : x = ε u := (ε.apply_symm_apply x).symm
    have hε1 : G6.coreAct 5 γ (ε u) = ε lu := by
      have h := hεπ ⟨γ, hγ⟩ u (hHU l u u.2)
      simpa [lu, l] using h.symm
    have hq1 : q (ε lu) = ε (T lu) := by
      rw [hq_apply, ε.symm_apply_apply]
    have hq2 : q (ε u) = ε (T u) := by
      rw [hq_apply, ε.symm_apply_apply]
    have hφl' : ((φ l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = γ :=
      congrArg Subtype.val hφl
    have htransγ : φ ⟨(a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹, hmem l⟩ =
        ⟨CFSG.OddStandard.rhoOf φ a * γ * (CFSG.OddStandard.rhoOf φ a)⁻¹,
          hsign γ hγ⟩ := by
      apply Subtype.ext
      have h := CFSG.OddStandard.rhoOf_transports φ a l ⟨_, hmem l⟩ rfl
      have h2 := congrArg (fun x : Equiv.Perm (Fin 5) =>
        (CFSG.OddStandard.rhoOf φ a) * x * (CFSG.OddStandard.rhoOf φ a)⁻¹) hφl'
      exact h.trans h2
    have hπγ' : ((π ⟨CFSG.OddStandard.rhoOf φ a * γ *
        (CFSG.OddStandard.rhoOf φ a)⁻¹, hsign γ hγ⟩ : ↥L₁) : MulAut W) =
        (a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹ := by
      have h1 : ((π (φ ⟨(a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹, hmem l⟩) :
            ↥L₁) : MulAut W) =
          ((π ⟨CFSG.OddStandard.rhoOf φ a * γ *
            (CFSG.OddStandard.rhoOf φ a)⁻¹, hsign γ hγ⟩ : ↥L₁) : MulAut W) :=
        congrArg (fun z : ↥(alternatingGroup (Fin 5)) =>
          ((π z : ↥L₁) : MulAut W)) htransγ
      have h2 : ((π (φ ⟨(a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹, hmem l⟩) :
            ↥L₁) : MulAut W) =
          (a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹ :=
        hπφ ⟨_, hmem l⟩
      exact h1.symm.trans h2
    have hR : G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a * γ *
        (CFSG.OddStandard.rhoOf φ a)⁻¹) (ε (T u)) = ε (T lu) := by
      let g' : ↥L₁ := π ⟨CFSG.OddStandard.rhoOf φ a * γ *
        (CFSG.OddStandard.rhoOf φ a)⁻¹, hsign γ hγ⟩
      let cl : ↥L₁ := ⟨(a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹, hmem l⟩
      have hgp : (g' : MulAut W) = (cl : MulAut W) := hπγ'
      have h := hεπ ⟨CFSG.OddStandard.rhoOf φ a * γ *
        (CFSG.OddStandard.rhoOf φ a)⁻¹, hsign γ hγ⟩ (T u) (hHU g' (T u) (T u).2)
      have h1 : (⟨(g' : MulAut W) ↑(T u), hHU g' (T u) (T u).2⟩ :
            ↥(matColSub β 0)) =
          ⟨(cl : MulAut W) ↑(T u), hHU cl (T u) (T u).2⟩ := by
        apply Subtype.ext
        exact congrArg (fun f : MulAut W => f (T u : W)) hgp
      have h2 : (⟨(cl : MulAut W) ↑(T u), hHU cl (T u) (T u).2⟩ :
            ↥(matColSub β 0)) = T lu := by
        apply Subtype.ext
        exact (hTact l u).symm
      calc G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a * γ *
              (CFSG.OddStandard.rhoOf φ a)⁻¹) (ε (T u))
          = ε ⟨(g' : MulAut W) ↑(T u), hHU g' (T u) (T u).2⟩ := h.symm
        _ = ε ⟨(cl : MulAut W) ↑(T u), hHU cl (T u) (T u).2⟩ := by rw [h1]
        _ = ε (T lu) := by rw [h2]
    show q (G6.coreAct 5 γ x) = G6.coreAct 5
      (CFSG.OddStandard.rhoOf φ a * γ * (CFSG.OddStandard.rhoOf φ a)⁻¹) (q x)
    rw [hx, hε1, hq1, hq2, hR]
  have hqeq : q = G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a) := by
    have hcomm : ∀ γ ∈ alternatingGroup (Fin 5),
        ((G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a))⁻¹ * q) * G6.coreAct 5 γ =
          G6.coreAct 5 γ *
            ((G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a))⁻¹ * q) := by
      intro γ hγ
      have h := hq_rel γ hγ
      calc ((G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a))⁻¹ * q) * G6.coreAct 5 γ
          = (G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a))⁻¹ * (q * G6.coreAct 5 γ) := by
              group
        _ = (G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a))⁻¹ *
              (G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a * γ *
                (CFSG.OddStandard.rhoOf φ a)⁻¹) * q) := by rw [h]
        _ = G6.coreAct 5 γ *
              ((G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a))⁻¹ * q) := by
              rw [map_mul, map_mul, map_inv]
              group
    have h1 := s15_T7_alt5_centralizer hcomm
    exact (inv_mul_eq_one.mp h1).symm
  have hTu : T u = u' := by
    apply Subtype.ext
    apply β.injective
    apply Multiplicative.toAdd.injective
    rw [hTβ u]
    exact hcol.symm
  calc ε u' = ε (T u) := by rw [hTu]
    _ = q (ε u) := by rw [hq_apply, ε.symm_apply_apply]
    _ = G6.coreAct 5 (CFSG.OddStandard.rhoOf φ a) (ε u) := by rw [hqeq]

private theorem coreAct_eq_of_pact_eq {x : Fin 5 → ZMod 2} (hx : isEven x)
    {σ τ : Equiv.Perm (Fin 5)} (h : pact σ x = pact τ x) :
    G6.coreAct 5 σ (s15T7OfEven ⟨x, (mem_evenWeight_iff x).mpr hx⟩) =
      G6.coreAct 5 τ (s15T7OfEven ⟨x, (mem_evenWeight_iff x).mpr hx⟩) := by
  have hσ : G6.coreAct 5 σ (s15T7OfEven ⟨x, (mem_evenWeight_iff x).mpr hx⟩) =
      s15T7OfEven ⟨pact σ x, pact_mem σ ((mem_evenWeight_iff x).mpr hx)⟩ :=
    (s15_T7_ofEven_vact σ ⟨x, (mem_evenWeight_iff x).mpr hx⟩).symm
  have hτ : G6.coreAct 5 τ (s15T7OfEven ⟨x, (mem_evenWeight_iff x).mpr hx⟩) =
      s15T7OfEven ⟨pact τ x, pact_mem τ ((mem_evenWeight_iff x).mpr hx)⟩ :=
    (s15_T7_ofEven_vact τ ⟨x, (mem_evenWeight_iff x).mpr hx⟩).symm
  rw [hσ, hτ]
  congr 1
  exact Subtype.ext h

private theorem pact_eq_of_coreAct_eq {x : Fin 5 → ZMod 2} (hx : isEven x)
    {σ τ : Equiv.Perm (Fin 5)}
    (h : G6.coreAct 5 σ (s15T7OfEven ⟨x, (mem_evenWeight_iff x).mpr hx⟩) =
      G6.coreAct 5 τ (s15T7OfEven ⟨x, (mem_evenWeight_iff x).mpr hx⟩)) :
    pact σ x = pact τ x := by
  have hσ := (s15_T7_ofEven_vact σ ⟨x, (mem_evenWeight_iff x).mpr hx⟩).symm
  have hτ := (s15_T7_ofEven_vact τ ⟨x, (mem_evenWeight_iff x).mpr hx⟩).symm
  rw [hσ, hτ] at h
  exact congrArg Subtype.val
    ((Function.LeftInverse.injective s15_T7_toEven_ofEven) h)

private theorem map_conj_mulAut_of_mul {H : Subgroup (MulAut W)} (x y : MulAut W) :
    H.map (MulAut.conj (x * y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem mul_mem_inf_normalizer_of_not_mem_normalizer
    {A : Subgroup (MulAut W)} {t a : MulAut W}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (ha₁ : IsAlt ↥L₁ 5) (ha₂ : IsAlt ↥L₂ 5)
    (hAX : A ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))
    (ht : L₂ = L₁.map (MulAut.conj t).toMonoidHom) (ha2 : a * a = 1)
    (ha : a ∈ A) (htA : t ∈ A)
    (hnorm : a ∉ Subgroup.normalizer (L₁ : Set (MulAut W))) :
    a * t ∈ A ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
  have hmap : L₁.map (MulAut.conj a).toMonoidHom = L₂ := by
    rcases CFSG.GroupTheory.AlternatingFive.map_conj_eq_or_eq_of_normalizes hcomm ha₁ ha₂
      (hAX ha) with h | h
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h) hnorm
    · exact h
  have hL1t : L₁.map (MulAut.conj t).toMonoidHom = L₂ := ht.symm
  have hL2a : L₂.map (MulAut.conj a).toMonoidHom = L₁ := by
    rw [← hmap, ← map_conj_mulAut_of_mul (H := L₁) a a, ha2]
    rw [show MulAut.conj (1 : MulAut W) = 1 from map_one _]
    exact Subgroup.map_id L₁
  refine Subgroup.mem_inf.mpr ⟨A.mul_mem ha htA, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc L₁.map (MulAut.conj (a * t)).toMonoidHom
      = (L₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
        map_conj_mulAut_of_mul (H := L₁) a t
    _ = L₂.map (MulAut.conj a).toMonoidHom := by rw [hL1t]
    _ = L₁ := hL2a

theorem swap_false_of_mem_aSet_two {Y A : Subgroup (MulAut W)}
    (hF : Nat.card F = 2) (hM : IsMatModel L₁ L₂ β ρ σ)
    (hO : AlternatingNatural L₁ (matColSub β 0) ⊥ 5)
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (ha₁ : IsAlt ↥L₁ 5) (ha₂ : IsAlt ↥L₂ 5)
    (hA : A ∈ E3.aSet 2 Y)
    (hAX : A ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))
    {t : MulAut W} (htA : t ∈ A) (ht : L₂ = L₁.map (MulAut.conj t).toMonoidHom) : False := by
  classical
  have hAmem : A ∈ E3.aSet 2 Y := hA
  obtain ⟨-, -, hAel, -⟩ := hA
  have ht2 : t * t = 1 := hAel.2 t htA
  have hAt : ∀ a ∈ A, a * t = t * a := fun a ha => hAel.1 a ha t htA
  obtain ⟨β', ρ', hM', hcol, htr⟩ := exists_transpose_model hF hM ht2 ht
  have hO' : AlternatingNatural L₁ (matColSub β' 0) ⊥ 5 := by rw [hcol]; exact hO
  obtain ⟨ε, φ, hε⟩ := exists_perm_column_of_congr_form hM' hO'
  let A₀ : Subgroup (MulAut W) := A ⊓ Subgroup.normalizer (L₁ : Set (MulAut W))
  let inc : ↥A₀ →* ↥(Subgroup.normalizer (L₁ : Set (MulAut W))) :=
    Subgroup.inclusion inf_le_right
  let s : ↥A₀ →* Equiv.Perm (Fin 5) := (CFSG.OddStandard.rhoOf φ).comp inc
  by_cases hcase : ∃ a : ↥A₀, s a ≠ 1
  ·
    have hs2 : ∀ g : ↥A₀, s g * s g = 1 := by
      intro g
      have hg : g * g = 1 := by
        apply Subtype.ext
        show (g : MulAut W) * (g : MulAut W) = 1
        rw [← pow_two]
        exact hAel.2 (g : MulAut W) g.2.1
      rw [← map_mul, hg, map_one]
    have hsc : ∀ g h : ↥A₀, s g * s h = s h * s g := by
      intro g h
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (g : MulAut W) * (h : MulAut W) = (h : MulAut W) * (g : MulAut W)
      exact hAel.1 (g : MulAut W) g.2.1 (h : MulAut W) h.2.1
    obtain ⟨x, hxeven, a₀, hxmove, horb⟩ := exists_orbit_two_of_perm s hs2 hsc hcase
    let xD : ↥(G6.coreMod 5) :=
      s15T7OfEven ⟨x, (mem_evenWeight_iff x).mpr hxeven⟩
    let y : ↥(matColSub β' 0) := ε.symm xD
    have hεy : ε y = xD := ε.apply_symm_apply xD
    let c : Fin 4 → F := fun i => Multiplicative.toAdd (β' (y : W)) i 0
    let w₀ : W := β'.symm (Multiplicative.ofAdd (Matrix.vecMulVec c c))
    have hβ'w : Multiplicative.toAdd (β' w₀) = Matrix.vecMulVec c c := by
      dsimp only [w₀]
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have htfix : t w₀ = w₀ := by
      apply β'.injective
      apply Multiplicative.toAdd.injective
      rw [htr w₀, hβ'w, Matrix.transpose_vecMulVec]
    have step : ∀ a : ↥A₀, ∃ u' : ↥(matColSub β' 0),
        ε u' = G6.coreAct 5 (s a) xD ∧
        Multiplicative.toAdd (β' ((a : MulAut W) w₀)) =
          Matrix.vecMulVec (fun i => Multiplicative.toAdd (β' (u' : W)) i 0)
            (fun i => Multiplicative.toAdd (β' (u' : W)) i 0) := by
      intro a
      have hanorm : (a : MulAut W) ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := a.2.2
      have haL1 : L₁.map (MulAut.conj (a : MulAut W)).toMonoidHom = L₁ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hanorm
      have hat : (a : MulAut W) * t = t * (a : MulAut W) := hAel.1 (a : MulAut W) a.2.1 t htA
      obtain ⟨B, hBunit, hBform⟩ :=
        exists_congr_form hF hM' htr (a := (a : MulAut W)) haL1 hat
      have hsupp : ∀ i k, k ≠ 0 →
          (B * Multiplicative.toAdd (β' (y : W))) i k = 0 := by
        intro i k hk
        rw [Matrix.mul_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [y.2 j k hk, mul_zero]
      let u' : ↥(matColSub β' 0) :=
        ⟨β'.symm (Multiplicative.ofAdd (B * Multiplicative.toAdd (β' (y : W)))), by
          intro i k hk
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
          exact hsupp i k hk⟩
      refine ⟨u', ?_, ?_⟩
      · have h := hε ⟨(a : MulAut W), hanorm⟩ B hBform y u' ?_
        · have hinc : inc a = ⟨(a : MulAut W), hanorm⟩ := Subtype.ext rfl
          simpa [u', hεy, s, hinc] using h
        · dsimp only [u']
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      · have hBw : Multiplicative.toAdd (β' ((a : MulAut W) w₀)) =
            B * Multiplicative.toAdd (β' w₀) * Bᵀ := hBform w₀
        have hcolvec : (fun i => Multiplicative.toAdd (β' (u' : W)) i 0) = B *ᵥ c := by
          funext i
          dsimp only [u']
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => rfl
        rw [hBw, hβ'w, hcolvec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
          Matrix.vecMul_transpose]
    have hA0step : ∀ a : ↥A₀,
        (a : MulAut W) w₀ = w₀ ∨ (a : MulAut W) w₀ = (a₀ : MulAut W) w₀ := by
      intro a
      obtain ⟨u', hεu', hwu'⟩ := step a
      rcases horb a with hx | hx
      · left
        have hc : G6.coreAct 5 (s a) xD = xD := by
          have h1 : pact (s a) x = pact (1 : Equiv.Perm (Fin 5)) x := by
            rw [pact_one]; exact hx
          have h2 := coreAct_eq_of_pact_eq hxeven h1
          simpa using h2
        have hy : u' = y := ε.injective (by rw [hεu', hc, hεy])
        apply β'.injective
        apply Multiplicative.toAdd.injective
        rw [hwu']
        have hcol : (fun i => Multiplicative.toAdd (β' (u' : W)) i 0) = c := by
          rw [hy]
        rw [hcol, hβ'w]
      · right
        obtain ⟨u₀', hεu₀', hwu₀'⟩ := step a₀
        have hc : G6.coreAct 5 (s a) xD = G6.coreAct 5 (s a₀) xD := by
          have h1 : pact (s a) x = pact (s a₀) x := hx
          exact coreAct_eq_of_pact_eq hxeven h1
        have huu : u' = u₀' := ε.injective (by rw [hεu', hc, hεu₀'])
        apply β'.injective
        apply Multiplicative.toAdd.injective
        rw [hwu', hwu₀', huu]
    have horbA : ∀ a ∈ A, a w₀ = w₀ ∨ a w₀ = (a₀ : MulAut W) w₀ := by
      intro a ha
      by_cases hnorm : a ∈ Subgroup.normalizer (L₁ : Set (MulAut W))
      · exact hA0step ⟨a, Subgroup.mem_inf.mpr ⟨ha, hnorm⟩⟩
      · have haa : a * a = 1 := by
          rw [← pow_two]
          exact hAel.2 a ha
        have hatmem := mul_mem_inf_normalizer_of_not_mem_normalizer hcomm ha₁ ha₂ hAX ht haa ha
          htA hnorm
        have h0 := hA0step ⟨a * t, hatmem⟩
        have haeq : a w₀ = (a * t) w₀ := by
          rw [MulAut.mul_apply W, htfix]
        rcases h0 with h | h
        · exact Or.inl (haeq.trans h)
        · exact Or.inr (haeq.trans h)
    have hmv : (a₀ : MulAut W) w₀ ≠ w₀ := by
      intro h
      obtain ⟨u₀', hεu₀', hwu₀'⟩ := step a₀
      have hsq : ∀ z : F, z * z = z := by
        intro z
        rcases CFSG.Quasithin.G64.eq_zero_or_eq_one_of_card_two hF z with hz | hz <;>
          rw [hz] <;> norm_num
      have hm : Matrix.vecMulVec (fun i => Multiplicative.toAdd (β' (u₀' : W)) i 0)
          (fun i => Multiplicative.toAdd (β' (u₀' : W)) i 0) = Matrix.vecMulVec c c := by
        rw [← hwu₀', congrArg (fun v => Multiplicative.toAdd (β' v)) h, hβ'w]
      have hdiag : ∀ i, Multiplicative.toAdd (β' (u₀' : W)) i 0 =
          Multiplicative.toAdd (β' (y : W)) i 0 := by
        intro i
        have hii := congrFun (congrFun hm i) i
        rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply] at hii
        rw [hsq, hsq] at hii
        exact hii
      have hmat : Multiplicative.toAdd (β' (u₀' : W)) = Multiplicative.toAdd (β' (y : W)) := by
        ext i k
        by_cases hk : k = 0
        · subst hk
          exact hdiag i
        · rw [u₀'.2 i k hk, y.2 i k hk]
      have huy : u₀' = y := by
        apply Subtype.ext
        apply β'.injective
        apply Multiplicative.toAdd.injective
        exact hmat
      have hcore : G6.coreAct 5 (s a₀) xD = xD := by
        rw [← hεu₀', huy, hεy]
      have hpact : pact (s a₀) x = pact (1 : Equiv.Perm (Fin 5)) x := by
        refine pact_eq_of_coreAct_eq hxeven ?_
        rw [hcore, show G6.coreAct 5 (1 : Equiv.Perm (Fin 5)) = 1 from map_one _]
        exact (MulAut.one_apply ↥(G6.coreMod 5) xD).symm
      rw [pact_one] at hpact
      exact hxmove hpact
    exact not_orbit_two_of_mem_aSet_two hAmem a₀.2.1 hmv horbA
  ·
    push Not at hcase
    have hcent : ∀ a : ↥A₀,
        (a : MulAut W) ∈ Subgroup.centralizer (L₁ : Set (MulAut W)) := by
      intro a
      have hsa : s a = 1 := hcase a
      have hinc : inc a = (⟨(a : MulAut W), a.2.2⟩ :
          ↥(Subgroup.normalizer (L₁ : Set (MulAut W)))) := Subtype.ext rfl
      have hker : (⟨(a : MulAut W), a.2.2⟩ :
          ↥(Subgroup.normalizer (L₁ : Set (MulAut W)))) ∈
          (CFSG.OddStandard.rhoOf φ).ker := by
        rw [← hinc, MonoidHom.mem_ker]
        simpa [s] using hsa
      rw [CFSG.OddStandard.rhoOf_ker, Subgroup.mem_subgroupOf] at hker
      exact hker
    have htriv : ∀ a : ↥A₀, (a : MulAut W) = 1 := by
      intro a
      have hanorm : (a : MulAut W) ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := a.2.2
      have haL1 : L₁.map (MulAut.conj (a : MulAut W)).toMonoidHom = L₁ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hanorm
      have hat : (a : MulAut W) * t = t * (a : MulAut W) := hAel.1 (a : MulAut W) a.2.1 t htA
      obtain ⟨B, hBunit, hBform⟩ :=
        exists_congr_form hF hM' htr (a := (a : MulAut W)) haL1 hat
      have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
      have hBmul : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBdet
      have hBTinv : Bᵀ * (B⁻¹)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul B hBdet, Matrix.transpose_one]
      have hcommB : ∀ l : ↥L₁,
          B * ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
            ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B := by
        intro l
        have hcl : (a : MulAut W) * (l : MulAut W) = (l : MulAut W) * (a : MulAut W) :=
          (Subgroup.mem_centralizer_iff.mp (hcent a) (l : MulAut W) l.2).symm
        have hact : ∀ v : W, (a : MulAut W) ((l : MulAut W) v) =
            (l : MulAut W) ((a : MulAut W) v) := by
          intro v
          have h := congrArg (fun f : MulAut W => f v) hcl
          simpa [MulAut.mul_apply] using h
        have hcommM : ∀ M : Matrix (Fin 4) (Fin 4) F,
            B * (((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) * M) * Bᵀ =
              ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) * (B * M * Bᵀ) := by
          intro M
          obtain ⟨v, rfl⟩ : ∃ v : W, Multiplicative.toAdd (β' v) = M :=
            ⟨β'.symm (Multiplicative.ofAdd M), by simp⟩
          have hL : Multiplicative.toAdd (β' ((a : MulAut W) ((l : MulAut W) v))) =
              B * (((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
                Matrix (Fin 4) (Fin 4) F) * Multiplicative.toAdd (β' v)) * Bᵀ := by
            rw [show Multiplicative.toAdd (β' ((a : MulAut W) ((l : MulAut W) v))) =
                B * Multiplicative.toAdd (β' ((l : MulAut W) v)) * Bᵀ from hBform _]
            rw [show Multiplicative.toAdd (β' ((l : MulAut W) v)) =
                ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
                  Matrix (Fin 4) (Fin 4) F) * Multiplicative.toAdd (β' v) from by
              simpa using congrArg Multiplicative.toAdd (hM'.hρ l v)]
          have hR : Multiplicative.toAdd (β' ((l : MulAut W) ((a : MulAut W) v))) =
              ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
                Matrix (Fin 4) (Fin 4) F) * (B * Multiplicative.toAdd (β' v) * Bᵀ) := by
            rw [show Multiplicative.toAdd (β' ((l : MulAut W) ((a : MulAut W) v))) =
                ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
                  Matrix (Fin 4) (Fin 4) F) * Multiplicative.toAdd (β' ((a : MulAut W) v)) from by
              simpa using congrArg Multiplicative.toAdd (hM'.hρ l ((a : MulAut W) v))]
            rw [hBform v]
          have hEq := congrArg Multiplicative.toAdd
            (congrArg β' (hact v))
          rw [hL, hR] at hEq
          exact hEq
        have hcommM' : ∀ M : Matrix (Fin 4) (Fin 4) F,
            B * ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) * M =
              ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) * B * M := by
          intro M
          have := congrArg (fun X => X * (B⁻¹)ᵀ) (hcommM M)
          simpa [Matrix.mul_assoc, hBTinv, Matrix.mul_one] using this
        have h1 := hcommM' 1
        simpa using h1
      have hφcomm : ∀ (l : ↥L₁) (w : Fin 4 → F),
          B *ᵥ (((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F).mulVec w) =
            ((ρ' l : Matrix.GeneralLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F).mulVec (B *ᵥ w) := by
        intro l w
        rw [Matrix.mulVec_mulVec, hcommB l, ← Matrix.mulVec_mulVec]
      let φB : (Fin 4 → F) →+ (Fin 4 → F) :=
        { toFun := fun w => B *ᵥ w
          map_zero' := by simp
          map_add' := fun x y => by rw [Matrix.mulVec_add] }
      obtain ⟨c, hc⟩ := hM'.comm_F φB (by
        intro l w
        exact hφcomm l w)
      have hBc : B = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
        refine CFSG.Quasithin.SwapModel.ext_of_mulVec_single fun j => ?_
        have h := hc (Pi.single j (1 : F))
        change B *ᵥ Pi.single j (1 : F) = c • Pi.single j (1 : F) at h
        rw [h, Matrix.smul_one_eq_diagonal]
        ext i
        simp [Matrix.mulVec_diagonal, Pi.smul_apply]
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hBunit.ne_zero
        rw [hBc, hc0, zero_smul]
      have hc1 : c = 1 := (CFSG.Quasithin.G64.eq_zero_or_eq_one_of_card_two hF c).resolve_left hc0
      have hB1 : B = 1 := by rw [hBc, hc1, one_smul]
      apply MulEquiv.ext
      intro v
      apply β'.injective
      apply Multiplicative.toAdd.injective
      rw [hBform v, hB1]
      simp
    let w₁ : W := β'.symm (Multiplicative.ofAdd (Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : F)))
    have hβ'w₁ : Multiplicative.toAdd (β' w₁) =
        Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : F) := by
      dsimp only [w₁]
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have htw : t w₁ ≠ w₁ := by
      intro h
      have h2 := congrArg (fun v => Multiplicative.toAdd (β' v)) h
      rw [htr w₁, hβ'w₁, Matrix.transpose_single] at h2
      have h3 := congrFun (congrFun h2 (0 : Fin 4)) (1 : Fin 4)
      simp at h3
    have horbA : ∀ a ∈ A, a w₁ = w₁ ∨ a w₁ = t w₁ := by
      intro a ha
      by_cases hnorm : a ∈ Subgroup.normalizer (L₁ : Set (MulAut W))
      · left
        have h1 : (⟨a, Subgroup.mem_inf.mpr ⟨ha, hnorm⟩⟩ : ↥A₀) = 1 :=
          Subtype.ext (htriv ⟨a, Subgroup.mem_inf.mpr ⟨ha, hnorm⟩⟩)
        have ha1 : a = 1 := congrArg Subtype.val h1
        rw [ha1]
        simp
      · right
        have haa : a * a = 1 := by
          rw [← pow_two]
          exact hAel.2 a ha
        have hatmem := mul_mem_inf_normalizer_of_not_mem_normalizer hcomm ha₁ ha₂ hAX ht haa ha
          htA hnorm
        have hat1 : (⟨a * t, hatmem⟩ : ↥A₀) = 1 :=
          Subtype.ext (htriv ⟨a * t, hatmem⟩)
        have hat : a * t = 1 := congrArg Subtype.val hat1
        have haeq : a = t := by
          calc a = a * 1 := (mul_one a).symm
            _ = a * (t * t) := by rw [ht2]
            _ = (a * t) * t := by group
            _ = 1 * t := by rw [hat]
            _ = t := one_mul t
        rw [haeq]
    exact not_orbit_two_of_mem_aSet_two hAmem htA htw horbA

end SwapColumn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
