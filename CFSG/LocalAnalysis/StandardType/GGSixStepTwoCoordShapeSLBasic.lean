module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeAlign
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType

namespace CoordSL

open CoordShape

section Aligned01

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {s p : ℕ} [Fact p.Prime]
  {hζ : AdjoinRoot.root g ^ p = 1}

theorem aligned_of_zero_one {β : Fin s → ZMod p} (hβ : ∀ i, β i = 0 ∨ β i = 1) :
    Aligned hζ β := by
  intro i j hj u _ hij
  rcases hβ j with h | h
  · exact absurd h hj
  · rcases hβ i with h' | h'
    · rw [h', h, mul_one] at hij
      exact absurd hij.symm u.ne_zero
    · rw [h', h]

end Aligned01

section FrameComp

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {s r p : ℕ}

@[expose] noncomputable def frameComp
    (φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)))
    (i j : Fin s) : AdjoinRoot g →ₗ[K] AdjoinRoot g :=
  LinearMap.proj i ∘ₗ LinearMap.fst K _ _ ∘ₗ φ ∘ₗ LinearMap.inl K _ _ ∘ₗ
    LinearMap.single K (fun _ => AdjoinRoot g) j

theorem frameComp_apply
    (φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)))
    (i j : Fin s) (y : AdjoinRoot g) : frameComp φ i j y = (φ (Pi.single j y, 0)).1 i :=
  rfl

theorem torusAct_single (k : Fin s → ℕ) (j : Fin s) (y : AdjoinRoot g) :
    torusAct g k ((Pi.single j y : Fin s → AdjoinRoot g), (0 : Fin r → K)) =
      (Pi.single j (AdjoinRoot.root g ^ k j * y), 0) := by
  refine Prod.ext (funext fun l => ?_) rfl
  change AdjoinRoot.root g ^ k l * (Pi.single j y : Fin s → AdjoinRoot g) l = _
  by_cases hl : l = j
  · subst hl
    simp
  · simp [hl]

theorem frameComp_intertwine
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    {t : Fin s → ZMod p}
    (hφ : ∀ x, φ (torusAct g (fun i => (t i).val) x) = torusAct g (fun i => (t i).val) (φ x))
    (i j : Fin s) (y : AdjoinRoot g) :
    frameComp φ i j (AdjoinRoot.root g ^ (t j).val * y) =
      AdjoinRoot.root g ^ (t i).val * frameComp φ i j y := by
  have h1 := hφ ((Pi.single j y : Fin s → AdjoinRoot g), (0 : Fin r → K))
  rw [torusAct_single] at h1
  rw [frameComp_apply, frameComp_apply]
  exact congrArg (fun v => v.1 i) h1

theorem torusAct_zero_fst (k : Fin s → ℕ) (w : Fin r → K) :
    torusAct g k ((0 : Fin s → AdjoinRoot g), w) = (0, w) :=
  Prod.ext (funext fun _ => mul_zero _) rfl

end FrameComp

section Joint

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {s r p : ℕ}
  [Fact p.Prime] {hζ : AdjoinRoot.root g ^ p = 1}
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {T : Set (Fin s → ZMod p)}
  {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}

omit [Finite K] in
theorem frameComp_of_jointRel (hζ₁ : AdjoinRoot.root g ^ p = 1)
    (hφ : ∀ t ∈ T, ∀ x, φ (torusAct g (fun i => (t i).val) x) =
      torusAct g (fun i => (t i).val) (φ x))
    {j : Fin s} {t₀ : Fin s → ZMod p} (ht₀ : t₀ ∈ T) (hj : t₀ j ≠ 0) {i : Fin s}
    (hij : ∀ t ∈ T, t i = t j) (x : AdjoinRoot g) :
    frameComp φ i j x = x * frameComp φ i j 1 := by
  refine mul_eq_of_intertwine hζ₁ hj (fun y => ?_) x
  have h := frameComp_intertwine (hφ t₀ ht₀) i j y
  rw [hij t₀ ht₀] at h
  exact h

include hprim in
theorem frameComp_eq_zero_of_not_jointRel
    (hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T) (hal : JointAligned (galExp g hζ) T)
    (hφ : ∀ t ∈ T, ∀ x, φ (torusAct g (fun i => (t i).val) x) =
      torusAct g (fun i => (t i).val) (φ x))
    {j : Fin s} {t₀ : Fin s → ZMod p} (ht₀ : t₀ ∈ T) (hj : t₀ j ≠ 0) {i : Fin s}
    (hij : ¬ ∀ t ∈ T, t i = t j) : frameComp φ i j = 0 := by
  obtain ⟨t, ht, ⟨htj, hti⟩ | ⟨htj, hti⟩⟩ := exists_sep hT hal ht₀ hj hij
  · exact eq_zero_of_intertwine hζ hprim htj hti (frameComp_intertwine (hφ t ht) i j)
  · ext y
    have h := frameComp_intertwine (hφ t ht) i j y
    rw [htj, ZMod.val_zero, pow_zero, one_mul] at h
    have h2 : (AdjoinRoot.root g ^ (t i).val - 1) * frameComp φ i j y = 0 := by
      rw [sub_mul, ← h, one_mul, sub_self]
    rw [LinearMap.zero_apply]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (root_pow_val_ne_one hprim hti))

omit [Finite K] in
include hprim in
theorem apply_single_snd_of_joint
    (hφ : ∀ t ∈ T, ∀ x, φ (torusAct g (fun i => (t i).val) x) =
      torusAct g (fun i => (t i).val) (φ x))
    {j : Fin s} {t₀ : Fin s → ZMod p} (ht₀ : t₀ ∈ T) (hj : t₀ j ≠ 0) (x : AdjoinRoot g) :
    (φ (Pi.single j x, 0)).2 = 0 := by
  set h : AdjoinRoot g →ₗ[K] (Fin r → K) := LinearMap.snd K _ _ ∘ₗ φ ∘ₗ LinearMap.inl K _ _ ∘ₗ
    LinearMap.single K (fun _ => AdjoinRoot g) j with hh
  have hhapp : ∀ y, h y = (φ (Pi.single j y, 0)).2 := fun y => rfl
  have hhint : ∀ y, h (AdjoinRoot.root g ^ (t₀ j).val * y) = h y := by
    intro y
    have h1 := hφ t₀ ht₀ ((Pi.single j y : Fin s → AdjoinRoot g), (0 : Fin r → K))
    rw [torusAct_single] at h1
    rw [hhapp, hhapp]
    have h2 := congrArg Prod.snd h1
    exact h2
  have hne : AdjoinRoot.root g ^ (t₀ j).val - 1 ≠ 0 :=
    sub_ne_zero.mpr (root_pow_val_ne_one hprim hj)
  have h1 : x = (AdjoinRoot.root g ^ (t₀ j).val - 1) *
      ((AdjoinRoot.root g ^ (t₀ j).val - 1)⁻¹ * x) := by
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [← hhapp, h1, sub_mul, one_mul, map_sub, hhint, sub_self]

omit [Finite K] in
include hprim in
theorem apply_jointFixed
    (hφ : ∀ t ∈ T, ∀ x, φ (torusAct g (fun i => (t i).val) x) =
      torusAct g (fun i => (t i).val) (φ x))
    {x : (Fin s → AdjoinRoot g) × (Fin r → K)} (hx : ∀ i, (∃ t ∈ T, t i ≠ 0) → x.1 i = 0)
    (i : Fin s) (hi : ∃ t ∈ T, t i ≠ 0) : (φ x).1 i = 0 := by
  obtain ⟨t, ht, hti⟩ := hi
  exact apply_fixed_of_comm hprim (hφ t ht) (fun k hk => hx k ⟨t, ht, hk⟩) hti

omit [Finite K] in
theorem torusAct_eq_self_of_jointFixed {β : Fin s → ZMod p}
    (hβ0 : ∀ i, (∀ t ∈ T, t i = 0) → β i = 0) {x : (Fin s → AdjoinRoot g) × (Fin r → K)}
    (hx : ∀ i, (∃ t ∈ T, t i ≠ 0) → x.1 i = 0) : torusAct g (fun i => (β i).val) x = x := by
  refine Prod.ext (funext fun i => ?_) rfl
  change AdjoinRoot.root g ^ (β i).val * x.1 i = x.1 i
  by_cases hi : ∃ t ∈ T, t i ≠ 0
  · rw [hx i hi, mul_zero]
  · push Not at hi
    rw [hβ0 i hi, ZMod.val_zero, pow_zero, one_mul]

include hprim in
theorem comm_torusAct_of_joint
    (hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T) (hal : JointAligned (galExp g hζ) T)
    (hφ : ∀ t ∈ T, ∀ x, φ (torusAct g (fun i => (t i).val) x) =
      torusAct g (fun i => (t i).val) (φ x))
    {β : Fin s → ZMod p} (hβ0 : ∀ i, (∀ t ∈ T, t i = 0) → β i = 0)
    (hβc : ∀ i j, (∀ t ∈ T, t i = t j) → β i = β j)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x) := by
  have hlin : φ ∘ₗ torusAct' g (fun i => (β i).val) = torusAct' g (fun i => (β i).val) ∘ₗ φ := by
    refine frame_ext (fun j y => ?_) (fun w => ?_)
    · simp only [LinearMap.comp_apply, torusAct'_apply]
      by_cases hj : ∃ t₀ ∈ T, t₀ j ≠ 0
      · obtain ⟨t₀, ht₀, hj⟩ := hj
        rw [torusAct_single]
        refine Prod.ext (funext fun i => ?_) ?_
        · change (φ (Pi.single j (AdjoinRoot.root g ^ (β j).val * y), 0)).1 i =
            AdjoinRoot.root g ^ (β i).val * (φ (Pi.single j y, 0)).1 i
          rw [← frameComp_apply, ← frameComp_apply]
          by_cases hij : ∀ t ∈ T, t i = t j
          · rw [frameComp_of_jointRel hζ hφ ht₀ hj hij, frameComp_of_jointRel hζ hφ ht₀ hj hij y,
              hβc i j hij]
            ring
          · rw [frameComp_eq_zero_of_not_jointRel hprim hT hal hφ ht₀ hj hij,
              LinearMap.zero_apply, LinearMap.zero_apply, mul_zero]
        · change (φ (Pi.single j (AdjoinRoot.root g ^ (β j).val * y), 0)).2 =
            (φ (Pi.single j y, 0)).2
          rw [apply_single_snd_of_joint hprim hφ ht₀ hj, apply_single_snd_of_joint hprim hφ ht₀ hj]
      · push Not at hj
        have hfix : ∀ i, (∃ t ∈ T, t i ≠ 0) →
            ((Pi.single j y : Fin s → AdjoinRoot g), (0 : Fin r → K)).1 i = 0 := by
          intro i ⟨t, ht, hti⟩
          have hij : i ≠ j := fun h => hti (by rw [h]; exact hj t ht)
          simp [hij]
        rw [torusAct_eq_self_of_jointFixed hβ0 hfix,
          torusAct_eq_self_of_jointFixed hβ0 (apply_jointFixed hprim hφ hfix)]
    · simp only [LinearMap.comp_apply, torusAct'_apply]
      have hfix : ∀ i, (∃ t ∈ T, t i ≠ 0) → ((0 : Fin s → AdjoinRoot g), w).1 i = 0 :=
        fun _ _ => rfl
      rw [torusAct_eq_self_of_jointFixed hβ0 hfix,
        torusAct_eq_self_of_jointFixed hβ0 (apply_jointFixed hprim hφ hfix)]
  have h := congrArg (fun f => f x) hlin
  exact h

include hprim in
theorem comm_nsSL_of_joint {n : ℕ} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {hC : (rootMat g).det = 1}
    (hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T) (hal : JointAligned (galExp g hζ) T)
    {u : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : ∀ t ∈ T, u * SLNS.nsSL ε hC (fun i => (t i).val) =
      SLNS.nsSL ε hC (fun i => (t i).val) * u)
    {β : Fin s → ZMod p} (hβ0 : ∀ i, (∀ t ∈ T, t i = 0) → β i = 0)
    (hβc : ∀ i j, (∀ t ∈ T, t i = t j) → β i = β j) :
    u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u := by
  have hφ : ∀ t ∈ T, ∀ x, frameForm g ε (u : Matrix (Fin n) (Fin n) K)
      (torusAct g (fun i => (t i).val) x) =
        torusAct g (fun i => (t i).val) (frameForm g ε (u : Matrix (Fin n) (Fin n) K) x) :=
    fun t ht => frameForm_torusAct_comm g ε (congrArg Subtype.val (hu t ht))
  apply Subtype.ext
  apply frameForm_injective g ε
  change frameForm g ε ((u : Matrix (Fin n) (Fin n) K) *
      SLNS.nsMat ε (rootMat g) (fun i => (β i).val)) =
    frameForm g ε (SLNS.nsMat ε (rootMat g) (fun i => (β i).val) *
      (u : Matrix (Fin n) (Fin n) K))
  rw [frameForm_mul, frameForm_mul, frameForm_nsMat']
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, torusAct'_apply]
  exact comm_torusAct_of_joint hprim hT hal hφ hβ0 hβc x

include hprim in
theorem commute_of_comm_blocks_joint {n : ℕ} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {hC : (rootMat g).det = 1}
    (hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T) (hal : JointAligned (galExp g hζ) T)
    {u v : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : ∀ t ∈ T, u * SLNS.nsSL ε hC (fun i => (t i).val) =
      SLNS.nsSL ε hC (fun i => (t i).val) * u)
    (hv : ∀ t ∈ T, v * SLNS.nsSL ε hC (fun i => (t i).val) =
      SLNS.nsSL ε hC (fun i => (t i).val) * v)
    (hZu : ∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε (jointSupp T) →
      y ∈ zeroCoords ε (jointSupp T) → u * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
        Matrix.SpecialLinearGroup.transvection hxy 1 * u)
    (hZv : ∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε (jointSupp T) →
      y ∈ zeroCoords ε (jointSupp T) → v * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
        Matrix.SpecialLinearGroup.transvection hxy 1 * v)
    (hcu : ∀ i j (hij : i ≠ j), (∀ t ∈ T, t i = t j) → (∃ t ∈ T, t i ≠ 0) →
      ∀ c : AdjoinRoot g, u * theta g ε (Matrix.SpecialLinearGroup.transvection hij c) =
        theta g ε (Matrix.SpecialLinearGroup.transvection hij c) * u)
    (hcv : ∀ i j (hij : i ≠ j), (∀ t ∈ T, t i = t j) → (∃ t ∈ T, t i ≠ 0) →
      ∀ c : AdjoinRoot g, v * theta g ε (Matrix.SpecialLinearGroup.transvection hij c) =
        theta g ε (Matrix.SpecialLinearGroup.transvection hij c) * v) :
    u * v = v * u := by
  have halZ : Aligned hζ (jointSupp T) := aligned_of_zero_one jointSupp_zero_or_one
  have hcolJ : ∀ (w : Matrix.SpecialLinearGroup (Fin n) K),
      (∀ t ∈ T, w * SLNS.nsSL ε hC (fun i => (t i).val) =
        SLNS.nsSL ε hC (fun i => (t i).val) * w) →
      (∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε (jointSupp T) → y ∈ zeroCoords ε (jointSupp T) →
        w * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
          Matrix.SpecialLinearGroup.transvection hxy 1 * w) →
      ∀ x ∈ zeroCoords ε (jointSupp T), (w : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single x 1 =
        (w : Matrix (Fin n) (Fin n) K) x x • Pi.single x 1 := by
    intro w hw hZw x hx
    have hwZ := comm_nsSL_of_joint hprim hT hal hw (fun i hi => jointSupp_eq_zero_iff.mpr hi)
      (fun i j hij => jointSupp_eq_of hij)
    funext z
    rw [Matrix.mulVec_single_one, Matrix.col_apply, col_of_mem_zeroCoords hprim halZ hwZ hZw hx z,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hscal : ∀ (w : Matrix.SpecialLinearGroup (Fin n) K),
      (∀ t ∈ T, w * SLNS.nsSL ε hC (fun i => (t i).val) =
        SLNS.nsSL ε hC (fun i => (t i).val) * w) →
      (∀ i j (hij : i ≠ j), (∀ t ∈ T, t i = t j) → (∃ t ∈ T, t i ≠ 0) →
        ∀ c : AdjoinRoot g, w * theta g ε (Matrix.SpecialLinearGroup.transvection hij c) =
          theta g ε (Matrix.SpecialLinearGroup.transvection hij c) * w) →
      ∀ i, (∃ t ∈ T, t i ≠ 0) → ∀ ξ : AdjoinRoot g,
        frameForm g ε (w : Matrix (Fin n) (Fin n) K) (Pi.single i ξ, 0) =
          (Pi.single i (ξ * (frameForm g ε (w : Matrix (Fin n) (Fin n) K)
            (Pi.single i 1, 0)).1 i), 0) := by
    intro w hw hcw i hi ξ
    obtain ⟨t₀, ht₀, hti⟩ := hi
    have halX : Aligned hζ (jointClass T i) := aligned_of_zero_one (jointClass_zero_or_one i)
    have hwX := comm_nsSL_of_joint hprim hT hal hw (β := jointClass T i)
      (fun k hk => jointClass_eq_zero_of_zero ht₀ hti hk) (fun k l hkl => jointClass_eq_of hkl)
    have hii : jointClass T i i = 1 := jointClass_eq_one_iff.mpr fun _ _ => rfl
    refine apply_single_eq_of_comm_theta hprim halX hwX (fun a b hab hβ hβ0 c => ?_)
      (by rw [hii]; exact one_ne_zero) ξ
    have ha1 : jointClass T i a = 1 := (jointClass_zero_or_one i a).resolve_left hβ0
    have ha : ∀ t ∈ T, t a = t i := jointClass_eq_one_iff.mp ha1
    have hb : ∀ t ∈ T, t b = t i := jointClass_eq_one_iff.mp (hβ.symm.trans ha1)
    exact hcw a b hab (fun t ht => (ha t ht).trans (hb t ht).symm)
      ⟨t₀, ht₀, by rw [ha t₀ ht₀]; exact hti⟩ c
  have key : ∀ x, ((u : Matrix (Fin n) (Fin n) K) * (v : Matrix (Fin n) (Fin n) K)) *ᵥ
      Pi.single x 1 =
        ((v : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K)) *ᵥ Pi.single x 1 := by
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    by_cases hx : x ∈ zeroCoords ε (jointSupp T)
    · rw [hcolJ v hv hZv x hx, hcolJ u hu hZu x hx, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hcolJ v hv hZv x hx, hcolJ u hu hZu x hx, smul_smul, smul_smul, mul_comm]
    · rcases hεx : ε x with ⟨a, i⟩ | j
      · have hi : ∃ t ∈ T, t i ≠ 0 := by
          by_contra h
          push Not at h
          exact hx ((mem_zeroCoords_inl hεx).mpr (jointSupp_eq_zero_iff.mpr h))
        have hxe : x = ε.symm (Sum.inl (a, i)) := by rw [← hεx, Equiv.symm_apply_apply]
        have hsu := hscal u hu hcu i hi
        have hsv := hscal v hv hcv i hi
        set b := (rootPB g).basis a with hb
        set μu := (frameForm g ε (u : Matrix (Fin n) (Fin n) K) (Pi.single i 1, 0)).1 i with hμu
        set μv := (frameForm g ε (v : Matrix (Fin n) (Fin n) K) (Pi.single i 1, 0)).1 i with hμv
        rw [hxe, ← frameCoords_single_basis, ← frameCoords_frameForm, ← frameCoords_frameForm,
          ← frameCoords_frameForm, ← frameCoords_frameForm, hsv b, hsu b, hsu (b * μv),
          hsv (b * μu), mul_right_comm]
      · exact absurd (mem_zeroCoords_inr hεx) hx
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext z x
  have h1 := congrFun (key x) z
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.col_apply] at h1

end Joint

end CoordSL

end CFSG.StandardType
