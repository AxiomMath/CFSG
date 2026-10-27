module

public import CFSG.Quasithin.Background.RonanH44Herm
public import CFSG.Quasithin.Background.RonanH44Par
public import CFSG.Quasithin.Background.RonanH44Perf

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB CFSG.Quasithin.G11.Harris.L2 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def IsFixedFieldEmb {F : Type} [Field F] (scalar : F →+* K) : Prop :=
  Nat.card F = 2 ^ n ∧
    ∀ coefficient : K, bar n coefficient = coefficient ↔
      ∃ fixedCoefficient : F, scalar fixedCoefficient = coefficient

@[expose] def NineOrthBlk {F : Type} [Field F] (scalar : F →+* K) (anisotropicCoefficient : F)
    (S : Subgroup (HMod n K)) (G : Subgroup (MulAut (HMod n K))) : Prop :=
  ∃ coordinates : ↥S ≃* Multiplicative (Fin 4 → F),
    (∀ (coefficient : F) (vector scaled : ↥S),
      mat (scaled : HMod n K) = scalar coefficient • mat (vector : HMod n K) →
      Multiplicative.toAdd (coordinates scaled) =
        coefficient • Multiplicative.toAdd (coordinates vector)) ∧
    (∀ vector : ↥S,
      (hermBlk (vector : HMod n K)).det =
        scalar (CFSG.Quasithin.H11Proof.orthMinus F anisotropicCoefficient
          (Multiplicative.toAdd (coordinates vector)))) ∧
    (∀ groupElement ∈ G,
      ∃ isometry ∈ CFSG.Quasithin.H11Proof.omegaFour F
          (CFSG.Quasithin.H11Proof.orthMinus F anisotropicCoefficient),
        ∀ vector image : ↥S,
          (image : HMod n K) = groupElement vector →
          coordinates image = isometry (coordinates vector)) ∧
    (∀ isometry ∈ CFSG.Quasithin.H11Proof.omegaFour F
          (CFSG.Quasithin.H11Proof.orthMinus F anisotropicCoefficient),
      ∃ groupElement ∈ G,
        ∀ vector image : ↥S,
          (image : HMod n K) = groupElement vector →
          coordinates image = isometry (coordinates vector))

@[expose] def blkMat (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => g (Fin.castLE (by decide) i) (Fin.castLE (by decide) j)

theorem det_blkMat_of_perfW {g : SL(3, K)} (hg : g ∈ perfW K) :
    (blkMat (g : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
  obtain ⟨h20, h21, h22⟩ := hg
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  rw [Matrix.det_fin_two]
  simp only [blkMat]
  simp [h20, h21, h22] at hdet ⊢
  linear_combination hdet

theorem hermBlk_twisted (X : HMod n K) :
    (hermBlk X)ᵀ = (hermBlk X).map (barR n K) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, hermBlk, barR_apply]
  exact (herm_apply X (Fin.castLE (by decide) j) (Fin.castLE (by decide) i)).symm

theorem hermBlk_mul (X Y : HMod n K) : hermBlk (X * Y) = hermBlk X + hermBlk Y := by
  ext i j
  simp [hermBlk, mat_mul]

theorem hermBlk_one : hermBlk (1 : HMod n K) = 0 := by
  ext i j
  simp [hermBlk, mat_one]

theorem eq_of_hermBlk_eq {X Y : HMod n K} (hX : X ∈ blkW n K) (hY : Y ∈ blkW n K)
    (h : hermBlk X = hermBlk Y) : X = Y := by
  obtain ⟨hX02, hX12, hX22⟩ := hX
  obtain ⟨hY02, hY12, hY22⟩ := hY
  have hX20 : mat X 2 0 = 0 := by rw [← herm_apply, hX02, map_zero]
  have hX21 : mat X 2 1 = 0 := by rw [← herm_apply, hX12, map_zero]
  have hY20 : mat Y 2 0 = 0 := by rw [← herm_apply, hY02, map_zero]
  have hY21 : mat Y 2 1 = 0 := by rw [← herm_apply, hY12, map_zero]
  apply mat_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · change mat X 0 2 = mat Y 0 2
    rw [hX02, hY02]
  · exact congrFun (congrFun h 1) 0
  · exact congrFun (congrFun h 1) 1
  · change mat X 1 2 = mat Y 1 2
    rw [hX12, hY12]
  · change mat X 2 0 = mat Y 2 0
    rw [hX20, hY20]
  · change mat X 2 1 = mat Y 2 1
    rw [hX21, hY21]
  · change mat X 2 2 = mat Y 2 2
    rw [hX22, hY22]

@[expose] noncomputable def blkHom (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(blkW n K) →* Multiplicative (twistedForm (barR n K)) where
  toFun X := Multiplicative.ofAdd ⟨hermBlk (X : HMod n K), hermBlk_twisted _⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hermBlk_one
  map_mul' X Y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hermBlk_mul _ _

theorem hermBlk_rho (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)}
    (hg : g ∈ stabW K) {X : HMod n K} (hX : X ∈ blkW n K) :
    rho hK g X ∈ blkW n K ∧
      hermBlk (rho hK g X) = blkMat (g : Matrix (Fin 3) (Fin 3) K) * hermBlk X *
        ((blkMat (g : Matrix (Fin 3) (Fin 3) K)).map (bar n))ᵀ := by
  obtain ⟨action, -, -, hentry, -, hact⟩ :=
    herm_parabolic_action (P := stabW K) (Q := QWs K) (S := blkW n K) rfl rfl rfl hn hK
  obtain ⟨hmem, hblk, -⟩ := hact ⟨g, hg⟩ X hX
  have hA : (action ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) =
      blkMat (g : Matrix (Fin 3) (Fin 3) K) := by
    ext r c
    exact hentry ⟨g, hg⟩ r c
  refine ⟨hmem, ?_⟩
  rw [hblk, hA]

theorem blkHom_injective : Function.Injective (blkHom n K) := by
  intro X Y h
  apply Subtype.ext
  apply eq_of_hermBlk_eq X.2 Y.2
  have h' := congrArg (fun z => (Multiplicative.toAdd z : twistedForm (barR n K)).1) h
  exact h'

theorem blkHom_surjective (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Function.Surjective (blkHom n K) := by
  obtain ⟨action, -, -, -, hblock, -⟩ :=
    herm_parabolic_action (P := stabW K) (Q := QWs K) (S := blkW n K) rfl rfl rfl hn hK
  intro Y
  have hY : ((Multiplicative.toAdd Y : twistedForm (barR n K)).1.map (bar n))ᵀ =
      (Multiplicative.toAdd Y : twistedForm (barR n K)).1 := by
    have h0 := (Multiplicative.toAdd Y : twistedForm (barR n K)).2
    have h1 : (Multiplicative.toAdd Y : twistedForm (barR n K)).1ᵀ =
        (Multiplicative.toAdd Y : twistedForm (barR n K)).1.map (barR n K) := h0
    ext i j
    have := congrFun (congrFun h1 j) i
    simp only [Matrix.transpose_apply, Matrix.map_apply, barR_apply] at this ⊢
    exact this.symm
  obtain ⟨X, hX, hXY⟩ := hblock _ hY
  refine ⟨⟨X, hX⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hXY

@[expose] noncomputable def blkEquiv (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ↥(blkW n K) ≃* Multiplicative (twistedForm (barR n K)) :=
  MulEquiv.ofBijective (blkHom n K) ⟨blkHom_injective, blkHom_surjective hn hK⟩

theorem toAdd_blkEquiv (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (X : ↥(blkW n K)) :
    ((Multiplicative.toAdd (blkEquiv hn hK X) : twistedForm (barR n K)) :
      Matrix (Fin 2) (Fin 2) K) = hermBlk (X : HMod n K) := rfl

theorem blkMat_embW (A : SL(2, K)) :
    blkMat (embW A : Matrix (Fin 3) (Fin 3) K) = (A : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat, embW]

theorem blk_rho_twist (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {g₀ : SL(3, K)}
    (hg₀ : g₀ ∈ stabW K) (A : SL(2, K))
    (hAg : (A : Matrix (Fin 2) (Fin 2) K) = blkMat (g₀ : Matrix (Fin 3) (Fin 3) K))
    (vector image : ↥(blkW n K)) (himg : (image : HMod n K) = rho hK g₀ (vector : HMod n K)) :
    (Multiplicative.toAdd (blkEquiv hn hK image) : twistedForm (barR n K)) =
      twistRep (barR_inv hK) A (Multiplicative.toAdd (blkEquiv hn hK vector)) := by
  apply Subtype.ext
  rw [twistRep_apply, toAdd_blkEquiv, toAdd_blkEquiv, himg, (hermBlk_rho hn hK hg₀ vector.2).2,
    hAg]
  rfl

theorem nineOrth_exists (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {S : Subgroup (HMod n K)} {G : Subgroup (MulAut (HMod n K))} (hS : S = blkW n K)
    (hG : G = perfectCore ((stabW K).map (rho hK))) :
    ∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ n ∧
      ∃ (scalar : F →+* K) (a : F), IsFixedFieldEmb (n := n) scalar ∧
        (∀ t : F, t ^ 2 + t + a ≠ 0) ∧ NineOrthBlk scalar a S G := by
  subst hS hG
  obtain ⟨ω, hω1⟩ := exists_trace_one hn hK
  have hω : barR n K ω ≠ ω := barR_ne_of_trace hK hω1
  have hb : coordB (barR_inv hK) ω = 1 := Subtype.ext hω1
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn) 2
  refine ⟨Fq n K, inferInstance, card_Fq hn hK, (frobFixed (barR n K)).subtype,
    coordC (barR_inv hK) ω, ⟨card_Fq hn hK, fun c => ?_⟩, fun t => ?_, ?_⟩
  · constructor
    · intro hc
      exact ⟨⟨c, mem_frobFixed.2 hc⟩, rfl⟩
    · rintro ⟨f, rfl⟩
      exact frobFixed_apply f
  · have := coordB_nonsplit (hinv := barR_inv hK) CharTwo.two_eq_zero hω t
    rwa [hb, one_mul] at this
  · obtain ⟨action, -, -, -, -, -⟩ :=
      herm_parabolic_action (P := stabW K) (Q := QWs K) (S := blkW n K) rfl rfl rfl hn hK
    obtain ⟨hA, hB⟩ := herm_omega hn hK hω hb
    set θ := theta hK hω with hθ
    refine ⟨(blkEquiv hn hK).trans (AddEquiv.toMultiplicative θ.symm.toAddEquiv), ?_, ?_, ?_, ?_⟩
    · intro c X Y h
      show θ.symm (Multiplicative.toAdd (blkEquiv hn hK Y)) =
        c • θ.symm (Multiplicative.toAdd (blkEquiv hn hK X))
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_smul, Subfield.smul_def, toAdd_blkEquiv, toAdd_blkEquiv]
      ext i j
      have := congrFun (congrFun h (Fin.castLE (by decide) i)) (Fin.castLE (by decide) j)
      simpa [hermBlk] using this
    · intro X
      have hx : θ (θ.symm (Multiplicative.toAdd (blkEquiv hn hK X))) =
          Multiplicative.toAdd (blkEquiv hn hK X) := θ.apply_symm_apply _
      have h1 := twistedDet_theta hK hω hb (θ.symm (Multiplicative.toAdd (blkEquiv hn hK X)))
      rw [hx] at h1
      have h2 := congrArg (fun z : Fq n K => (z : K)) h1
      simp only [twistedDet_apply] at h2
      exact (toAdd_blkEquiv hn hK X ▸ h2 : _)
    · intro g hg
      have hg' : g ∈ (perfectCore (stabW K)).map (rho hK) := by
        rw [map_perfectCore]
        exact hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg'
      have hg₀W : g₀ ∈ perfW K := perfectCore_stabW_le hg₀
      have hg₀S : g₀ ∈ stabW K := ⟨hg₀W.1, hg₀W.2.1⟩
      obtain ⟨φ, hφ, hφx⟩ := hA ⟨blkMat (g₀ : Matrix (Fin 3) (Fin 3) K),
        det_blkMat_of_perfW hg₀W⟩
      refine ⟨φ, hφ, fun vector image himg => ?_⟩
      have hr := blk_rho_twist hn hK hg₀S ⟨blkMat (g₀ : Matrix (Fin 3) (Fin 3) K),
        det_blkMat_of_perfW hg₀W⟩ rfl vector image himg
      have hx : θ (θ.symm (Multiplicative.toAdd (blkEquiv hn hK vector))) =
          Multiplicative.toAdd (blkEquiv hn hK vector) := θ.apply_symm_apply _
      have h1 := hφx (θ.symm (Multiplicative.toAdd (blkEquiv hn hK vector)))
      rw [hx, ← hr] at h1
      apply Multiplicative.toAdd.injective
      exact h1
    · intro φ hφ
      obtain ⟨A, hAφ⟩ := hB φ hφ
      have hemb : embW A ∈ perfectCore (stabW K) := embW_mem_perfectCore h4 A
      have hembW : embW A ∈ perfW K := embW_mem_perfW A
      have hembS : embW A ∈ stabW K := ⟨hembW.1, hembW.2.1⟩
      refine ⟨rho hK (embW A), ?_, fun vector image himg => ?_⟩
      · rw [← map_perfectCore]
        exact ⟨embW A, hemb, rfl⟩
      · have hr := blk_rho_twist hn hK hembS A (blkMat_embW A).symm vector image himg
        have hx : θ (θ.symm (Multiplicative.toAdd (blkEquiv hn hK vector))) =
            Multiplicative.toAdd (blkEquiv hn hK vector) := θ.apply_symm_apply _
        have h1 := hAφ (θ.symm (Multiplicative.toAdd (blkEquiv hn hK vector)))
        rw [hx, ← hr] at h1
        apply Multiplicative.toAdd.injective
        exact h1

end CFSG.Quasithin.RonanH44
