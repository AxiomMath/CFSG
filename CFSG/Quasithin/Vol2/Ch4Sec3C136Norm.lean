module

public import CFSG.Quasithin.Vol2.Ch4Sec3NatMod

public section

namespace CFSG.Quasithin.H13.Ch4

open Matrix

section Commutant

variable {F : Type} [Field F]

theorem exists_smul_of_commute (φ : (Fin 3 → F) →+ (Fin 3 → F))
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F) (v : Fin 3 → F),
      φ ((SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec (φ v)) :
    ∃ c : F, ∀ v, φ v = c • v := by
  classical
  have key : ∀ (i j : Fin 3), i ≠ j → ∀ b : F,
      φ (Pi.single i b) = Pi.single i (b * φ (Pi.single j 1) j) := by
    intro i j hij b
    have h1 := h i j hij b (Pi.single j 1)
    rw [transvection_mulVec, transvection_mulVec, map_add] at h1
    have h2 := add_left_cancel h1
    simpa using h2
  set c := φ (Pi.single 0 1) 0 with hc
  have hall : ∀ j : Fin 3, φ (Pi.single j 1) j = c := by
    intro j
    by_cases hj : j = 0
    · rw [hj]
    · have h1 := congrFun (key 0 j (Ne.symm hj) 1) 0
      simp only [Pi.single_eq_same, one_mul] at h1
      rw [hc, h1]
  have hsingle : ∀ (i : Fin 3) (b : F), φ (Pi.single i b) = Pi.single i (b * c) := by
    intro i b
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := by
      by_cases h0 : i = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun h' => h0 h'.symm⟩
    rw [key i j (Ne.symm hj) b, hall j]
  refine ⟨c, fun v => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  simp_rw [hsingle]
  funext l
  rw [Finset.sum_apply]
  simp [Pi.single_apply, mul_comm]

theorem injective_of_intertwine (φ : (Fin 3 → F) →+ (Fin 3 → F))
    (h : ∀ X : SpecialLinearGroup (Fin 3) F, ∃ Y : SpecialLinearGroup (Fin 3) F,
      ∀ v, φ ((X : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        (Y : Matrix (Fin 3) (Fin 3) F).mulVec (φ v))
    (h0 : φ ≠ 0) : Function.Injective φ := by
  classical
  refine (injective_iff_map_eq_zero φ).mpr fun v hv => ?_
  by_contra hv0
  apply h0
  have hinv : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F) (w : Fin 3 → F), w ∈ φ.ker →
      (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ φ.ker := by
    intro i j hij b w hw
    obtain ⟨Y, hY⟩ := h (SpecialLinearGroup.transvection hij b)
    rw [AddMonoidHom.mem_ker] at hw ⊢
    rw [hY, hw, mulVec_zero]
  have htop := eq_top_of_transvection_invariant φ.ker hinv (AddMonoidHom.mem_ker.mpr hv) hv0
  refine AddMonoidHom.ext fun w => ?_
  have hw : w ∈ φ.ker := by rw [htop]; trivial
  simpa using hw

end Commutant

section NormalForm

variable {F : Type} [Field F] {k : ℕ}

@[expose] def dact (X : Matrix (Fin 3) (Fin 3) F) (v : Fin k → Fin 3 → F) : Fin k → Fin 3 → F :=
  fun i => X.mulVec (v i)

@[expose] def NormalizesDact (T : (Fin k → Fin 3 → F) → (Fin k → Fin 3 → F)) : Prop :=
  ∀ X : SpecialLinearGroup (Fin 3) F, ∃ Y : SpecialLinearGroup (Fin 3) F, ∀ v,
    T (dact (X : Matrix (Fin 3) (Fin 3) F) v) = dact (Y : Matrix (Fin 3) (Fin 3) F) (T v)

@[expose] def dactBlock (T : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F)) (i j : Fin k) :
    (Fin 3 → F) →+ (Fin 3 → F) :=
  (Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i).comp
    (T.comp (AddMonoidHom.single (fun _ : Fin k => Fin 3 → F) j))

theorem dactBlock_apply (T : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F)) (i j : Fin k)
    (x : Fin 3 → F) : dactBlock T i j x = T (Pi.single j x) i := rfl

theorem apply_eq_sum_dactBlock (T : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F))
    (v : Fin k → Fin 3 → F) (i : Fin k) : T v i = ∑ j, dactBlock T i j (v j) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, Finset.sum_apply]
  rfl

theorem dact_single (X : Matrix (Fin 3) (Fin 3) F) (j : Fin k) (x : Fin 3 → F) :
    dact X (Pi.single j x) = Pi.single j (X.mulVec x) := by
  classical
  funext l
  by_cases h : l = j
  · subst h
    simp [dact]
  · simp [dact, h]

theorem dactBlock_intertwine {T : (Fin k → Fin 3 → F) ≃+ (Fin k → Fin 3 → F)}
    {X Y : Matrix (Fin 3) (Fin 3) F} (h : ∀ v, T (dact X v) = dact Y (T v)) (i j : Fin k)
    (x : Fin 3 → F) :
    dactBlock T.toAddMonoidHom i j (X.mulVec x) = Y.mulVec (dactBlock T.toAddMonoidHom i j x) := by
  show T (Pi.single j (X.mulVec x)) i = Y.mulVec (T (Pi.single j x) i)
  rw [← dact_single, h]
  rfl

theorem exists_normalForm [Finite F] (hk : k ≠ 0)
    {T : (Fin k → Fin 3 → F) ≃+ (Fin k → Fin 3 → F)} (hT : NormalizesDact ⇑T)
    (hT' : NormalizesDact ⇑T.symm) :
    ∃ (ψ : (Fin 3 → F) ≃+ (Fin 3 → F)) (σ : F ≃+* F) (c : Matrix (Fin k) (Fin k) F),
      (∀ (μ : F) (x : Fin 3 → F), ψ (μ • x) = σ μ • ψ x) ∧
      ∀ v i, T v i = ∑ j, c i j • ψ (v j) := by
  classical
  set B := dactBlock T.toAddMonoidHom with hB
  have hrev : ∀ Y : SpecialLinearGroup (Fin 3) F, ∃ X : SpecialLinearGroup (Fin 3) F, ∀ v,
      T (dact (X : Matrix (Fin 3) (Fin 3) F) v) = dact (Y : Matrix (Fin 3) (Fin 3) F) (T v) := by
    intro Y
    obtain ⟨X, hX⟩ := hT' Y
    refine ⟨X, fun v => ?_⟩
    have h1 := hX (T v)
    rw [AddEquiv.symm_apply_apply] at h1
    rw [← h1, AddEquiv.apply_symm_apply]
  obtain ⟨i₀, j₀, hne⟩ : ∃ i₀ j₀, B i₀ j₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let j₁ : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
    have h1 : T (Pi.single j₁ (Pi.single 0 1)) = 0 := by
      funext i
      have h2 := congrArg (fun φ : (Fin 3 → F) →+ (Fin 3 → F) => φ (Pi.single 0 1)) (hcon i j₁)
      simpa [hB, dactBlock_apply] using h2
    have h2 := T.injective (h1.trans (map_zero T).symm)
    have h3 := congrFun (congrFun h2 j₁) 0
    simp at h3
  have hint : ∀ (X Y : SpecialLinearGroup (Fin 3) F),
      (∀ v, T (dact (X : Matrix (Fin 3) (Fin 3) F) v) = dact (Y : Matrix (Fin 3) (Fin 3) F) (T v)) →
      ∀ i j x, B i j ((X : Matrix (Fin 3) (Fin 3) F).mulVec x) =
        (Y : Matrix (Fin 3) (Fin 3) F).mulVec (B i j x) :=
    fun X Y h i j x => dactBlock_intertwine h i j x
  have hinj : Function.Injective (B i₀ j₀) := by
    refine injective_of_intertwine (B i₀ j₀) (fun X => ?_) hne
    obtain ⟨Y, hY⟩ := hT X
    exact ⟨Y, fun v => hint X Y hY i₀ j₀ v⟩
  have hsurj : Function.Surjective (B i₀ j₀) := Finite.injective_iff_surjective.mp hinj
  set ψ : (Fin 3 → F) ≃+ (Fin 3 → F) := AddEquiv.ofBijective (B i₀ j₀) ⟨hinj, hsurj⟩ with hψ
  have hψapp : ∀ x, ψ x = B i₀ j₀ x := fun _ => rfl
  have hψinv : ∀ (X Y : SpecialLinearGroup (Fin 3) F),
      (∀ v, T (dact (X : Matrix (Fin 3) (Fin 3) F) v) = dact (Y : Matrix (Fin 3) (Fin 3) F) (T v)) →
      ∀ w, ψ.symm ((Y : Matrix (Fin 3) (Fin 3) F).mulVec w) =
        (X : Matrix (Fin 3) (Fin 3) F).mulVec (ψ.symm w) := by
    intro X Y h w
    apply ψ.injective
    rw [AddEquiv.apply_symm_apply, hψapp, hint X Y h, ← hψapp, AddEquiv.apply_symm_apply]
  have hcomm : ∀ φ : (Fin 3 → F) →+ (Fin 3 → F),
      (∀ (X Y : SpecialLinearGroup (Fin 3) F),
        (∀ v, T (dact (X : Matrix (Fin 3) (Fin 3) F) v) =
          dact (Y : Matrix (Fin 3) (Fin 3) F) (T v)) →
        ∀ w, φ ((Y : Matrix (Fin 3) (Fin 3) F).mulVec w) =
          (Y : Matrix (Fin 3) (Fin 3) F).mulVec (φ w)) →
      ∃ c : F, ∀ w, φ w = c • w := by
    intro φ hφ
    refine exists_smul_of_commute φ fun i j hij b w => ?_
    obtain ⟨X, hX⟩ := hrev (SpecialLinearGroup.transvection hij b)
    exact hφ X _ hX w
  have hblk : ∀ i j, ∃ c : F, ∀ x, B i j x = c • ψ x := by
    intro i j
    obtain ⟨c, hc⟩ := hcomm ((B i j).comp ψ.symm.toAddMonoidHom) (fun X Y h w => by
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
      rw [hψinv X Y h, hint X Y h])
    refine ⟨c, fun x => ?_⟩
    have h1 := hc (ψ x)
    simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
      AddEquiv.symm_apply_apply] at h1
    exact h1
  choose c hc using hblk
  have hsc : ∀ μ : F, ∃ s : F, ∀ x, ψ (μ • x) = s • ψ x := by
    intro μ
    let m : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun x => μ • x, map_zero' := smul_zero μ, map_add' := smul_add μ }
    obtain ⟨s, hs⟩ := hcomm (ψ.toAddMonoidHom.comp (m.comp ψ.symm.toAddMonoidHom))
      (fun X Y h w => by
        show ψ (μ • ψ.symm ((Y : Matrix (Fin 3) (Fin 3) F).mulVec w)) =
          (Y : Matrix (Fin 3) (Fin 3) F).mulVec (ψ (μ • ψ.symm w))
        rw [hψinv X Y h, ← Matrix.mulVec_smul, hψapp, hint X Y h, ← hψapp])
    refine ⟨s, fun x => ?_⟩
    have h1 := hs (ψ x)
    have h2 : ψ (μ • ψ.symm (ψ x)) = s • ψ x := h1
    rwa [AddEquiv.symm_apply_apply] at h2
  choose s hs using hsc
  set e : Fin 3 → F := Pi.single 0 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he] at this
  have huniq : ∀ a b : F, a • e = b • e → a = b := fun a b h => smul_left_injective F he0 h
  have hse : ∀ μ, s μ • e = ψ (μ • ψ.symm e) := by
    intro μ
    rw [hs, AddEquiv.apply_symm_apply]
  have hadd : ∀ μ ν, s (μ + ν) = s μ + s ν := by
    intro μ ν
    apply huniq
    rw [hse, add_smul, map_add, ← hse, ← hse, add_smul]
  have hmul : ∀ μ ν, s (μ * ν) = s μ * s ν := by
    intro μ ν
    apply huniq
    rw [hse, mul_smul, hs, ← hse, mul_smul]
  have hone : s 1 = 1 := by
    apply huniq
    rw [hse, one_smul, one_smul, AddEquiv.apply_symm_apply]
  have hzero : s 0 = 0 := by
    have h1 := hadd 0 0
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsinj : Function.Injective s := by
    intro μ ν h
    have hv0 : ψ.symm e ≠ 0 := fun h0 => he0 (by rw [← ψ.apply_symm_apply e, h0, map_zero])
    have h1 : ψ (μ • ψ.symm e) = ψ (ν • ψ.symm e) := by rw [hs, hs, h]
    exact smul_left_injective F hv0 (ψ.injective h1)
  let σ₀ : F →+* F :=
    { toFun := s, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd }
  have hσinj : Function.Injective σ₀ := hsinj
  refine ⟨ψ, RingEquiv.ofBijective σ₀ ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩,
    Matrix.of c, fun μ x => hs μ x, fun v i => ?_⟩
  have h1 := apply_eq_sum_dactBlock T.toAddMonoidHom v i
  rw [AddEquiv.coe_toAddMonoidHom] at h1
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.of_apply]; exact hc i j (v j)

theorem exists_semilinear [Finite F] (hk : k ≠ 0)
    {T : (Fin k → Fin 3 → F) ≃+ (Fin k → Fin 3 → F)} (hT : NormalizesDact ⇑T)
    (hT' : NormalizesDact ⇑T.symm) :
    ∃ σ : F ≃+* F, ∀ (μ : F) (v : Fin k → Fin 3 → F), T (μ • v) = σ μ • T v := by
  obtain ⟨ψ, σ, c, hψ, hTc⟩ := exists_normalForm hk hT hT'
  refine ⟨σ, fun μ v => funext fun i => ?_⟩
  rw [hTc, Pi.smul_apply, hTc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, hψ, smul_comm]

theorem exists_matrix_normalForm [Finite F] (hk : k ≠ 0)
    {T : (Fin k → Fin 3 → F) ≃+ (Fin k → Fin 3 → F)} (hT : NormalizesDact ⇑T)
    (hT' : NormalizesDact ⇑T.symm) (hlin : ∀ (μ : F) (v : Fin k → Fin 3 → F), T (μ • v) = μ • T v) :
    ∃ (P : Matrix (Fin 3) (Fin 3) F) (c : Matrix (Fin k) (Fin k) F),
      ∀ v i, T v i = ∑ j, c i j • P.mulVec (v j) := by
  obtain ⟨ψ, σ, c, hψ, hTc⟩ := exists_normalForm hk hT hT'
  set w : Fin k → Fin 3 → F := fun _ => Pi.single 0 1 with hw
  have hw0 : w ≠ 0 := by
    intro h
    have := congrFun (congrFun h ⟨0, Nat.pos_of_ne_zero hk⟩) 0
    simp [hw] at this
  have hσ : ∀ μ, σ μ = μ := by
    intro μ
    have h1 : T (μ • T.symm w) = σ μ • T (T.symm w) := by
      funext i
      rw [hTc, Pi.smul_apply, hTc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, hψ, smul_comm]
    rw [hlin, AddEquiv.apply_symm_apply] at h1
    exact (smul_left_injective F hw0 h1).symm
  let ψl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := ψ
      map_add' := map_add ψ
      map_smul' := fun μ x => by rw [hψ, hσ]; rfl }
  refine ⟨LinearMap.toMatrix' ψl, c, fun v i => ?_⟩
  rw [hTc]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.toMatrix'_mulVec]
  rfl

end NormalForm

end CFSG.Quasithin.H13.Ch4
