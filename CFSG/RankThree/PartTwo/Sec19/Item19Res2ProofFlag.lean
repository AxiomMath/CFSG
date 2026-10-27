module

public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.RankThree.PartTwo.Sec19.Statements
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open Matrix Module CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)

section Hom

theorem isProperParabolic_comap {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (hf : Function.Surjective f) {P : Subgroup Y} (hP : IsProperParabolic P) :
    IsProperParabolic (P.comap f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPtop, T, hT⟩ := hP
  refine ⟨fun h => hPtop ?_, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hf y
    have : x ∈ P.comap f := h ▸ Subgroup.mem_top x
    exact this
  · obtain ⟨T', hT'⟩ := Sylow.mapSurjective_surjective hf 2 T
    refine ⟨T', fun z hz => hT ?_⟩
    have h1 : f z ∈ (Subgroup.normalizer ((T' : Subgroup X) : Set X)).map f :=
      Subgroup.mem_map_of_mem f hz
    have h2 := Subgroup.le_normalizer_map f h1
    rw [← Sylow.coe_mapSurjective hf, hT'] at h2
    exact h2

theorem isProperParabolic_map_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) {R : Subgroup X} (hR : IsProperParabolic R)
    (hker : f.ker ≤ R) : IsProperParabolic (R.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRtop, T, hT⟩ := hR
  refine ⟨fun h => hRtop ?_, Sylow.mapSurjective hf T, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : f x ∈ R.map f := h ▸ Subgroup.mem_top (f x)
    obtain ⟨r, hr, hrx⟩ := hx
    have hk : r⁻¹ * x ∈ R := hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hrx, inv_mul_cancel])
    simpa using R.mul_mem hr hk
  · intro y hy
    obtain ⟨g, rfl⟩ := hf y
    rw [Sylow.coe_mapSurjective] at hy
    set M : Subgroup X := ((T : Subgroup X).map f).comap f with hM
    have hTM : (T : Subgroup X) ≤ M := Subgroup.le_comap_map f _
    have hgTM : ((g • T : Sylow 2 X) : Subgroup X) ≤ M := by
      intro z hz
      change z ∈ ((g • T : Sylow 2 X) : Subgroup X) at hz
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      change f (g * t * g⁻¹) ∈ (T : Subgroup X).map f
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy (f t)).mp ⟨t, ht, rfl⟩
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (T.subtype hTM) ((g • T).subtype hgTM)
    rw [Sylow.smul_subtype] at hm
    have hm' : (m : X) • T = g • T := Sylow.subtype_injective hm
    have hn : (m : X)⁻¹ * g ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
      refine Sylow.smul_eq_iff_mem_normalizer.mp ?_
      rw [mul_smul, ← hm', inv_smul_smul]
    obtain ⟨t, ht, htm⟩ := (m.2 : (m : X) ∈ M)
    refine ⟨t * ((m : X)⁻¹ * g), hT (Subgroup.mul_mem _ (Subgroup.le_normalizer ht) hn), ?_⟩
    rw [map_mul, htm, map_mul, map_inv, mul_inv_cancel_left]

theorem isProperParabolic_map_equiv {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    {P : Subgroup X} (hP : IsProperParabolic P) : IsProperParabolic (P.map e.toMonoidHom) := by
  refine isProperParabolic_map_of_surjective e.toMonoidHom e.surjective hP ?_
  intro x hx
  have : x = 1 := e.injective (by rw [map_one]; exact hx)
  rw [this]
  exact Subgroup.one_mem _

end Hom

section Flag

variable {F : Type} [Field F] {n : ℕ}

theorem apply_three {σ : F ≃+* F} (hσ : orderOf σ = 3) (x : F) : σ (σ (σ x)) = x := by
  have h := congrArg (fun τ : F ≃+* F => τ x) (pow_orderOf_eq_one σ)
  rw [hσ] at h
  simpa [pow_succ] using h

theorem map_mulVec_comp (σ : F ≃+* F) (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    A.map σ *ᵥ (⇑σ ∘ v) = ⇑σ ∘ (A *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec (σ : F →+* F) A v i).symm

theorem exists_fixed_mem_not_le [Finite F] {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {W W' : Submodule F (Fin n → F)} (hW : ∀ v ∈ W, ⇑σ ∘ v ∈ W) (hle : ¬ W ≤ W') :
    ∃ v ∈ W, v ∉ W' ∧ ⇑σ ∘ v = v := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' F
  let a : W ≃+ W :=
    { toFun := fun w => ⟨⇑σ ∘ (w : Fin n → F), hW _ w.2⟩
      invFun := fun w => ⟨⇑σ ∘ ⇑σ ∘ (w : Fin n → F), hW _ (hW _ w.2)⟩
      left_inv := fun w => Subtype.ext (funext fun i => apply_three hσ _)
      right_inv := fun w => Subtype.ext (funext fun i => apply_three hσ _)
      map_add' := fun w w' => Subtype.ext (funext fun i => by simp) }
  have ha : ∀ (c : F) (v : W), a (c • v) = σ c • a v := fun c v =>
    Subtype.ext (funext fun i => by simp [a])
  have hah : ∀ v : W, (⇑a)^[3] v = v := fun v =>
    Subtype.ext (funext fun i => by simp [a, apply_three hσ])
  obtain ⟨-, -, -, -, b, hb, -⟩ := CFSG.RankThree.Classical.semilinear_fixed_basis hℓ e.pos
    (by rw [Nat.card_eq_fintype_card, hcard]) σ hσ (V := W) rfl a ha hah
  by_contra hcon
  push Not at hcon
  apply hle
  have hbW' : ∀ i, ((b i : W) : Fin n → F) ∈ W' := fun i => by
    by_contra h
    exact hcon _ (b i).2 h (congrArg Subtype.val (hb i))
  intro w hw
  have hsum := b.sum_repr ⟨w, hw⟩
  have h1 : w = ∑ i, (b.repr ⟨w, hw⟩ i) • ((b i : W) : Fin n → F) := by
    have := congrArg Subtype.val hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  rw [h1]
  exact W'.sum_mem fun i _ => W'.smul_mem _ (hbW' i)

theorem exists_fixed_map_standardFlag_eq [Finite F] {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {V : Fin (n + 1) → Submodule F (Fin n → F)} (hV : IsCompleteFlag V)
    (hVσ : ∀ i, ∀ v ∈ V i, ⇑σ ∘ v ∈ V i) :
    ∃ g : SpecialLinearGroup (Fin n) F,
      (g : Matrix (Fin n) (Fin n) F).map σ = g ∧ ∀ i : Fin (n + 1),
      (flagSpace n F i).map (mulVecLin (g : Matrix (Fin n) (Fin n) F)) = V i := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by ext i; exact i.elim0, fun i => Subsingleton.elim _ _⟩
  have hlt : ∀ c : Fin n, V c.castSucc < V c.succ := fun c => by
    refine lt_of_le_of_ne (hV.1 (Fin.castSucc_le_succ c)) fun h => ?_
    have := congrArg (fun W : Submodule F (Fin n → F) => finrank F W) h
    simp only [hV.2, Fin.val_castSucc, Fin.val_succ] at this
    omega
  have hex : ∀ c : Fin n, ∃ v ∈ V c.succ, v ∉ V c.castSucc ∧ ⇑σ ∘ v = v :=
    fun c => exists_fixed_mem_not_le hσ (hVσ c.succ) (not_le_of_gt (hlt c))
  choose v hvV hvnot hvfix using hex
  have hspan : ∀ i : ℕ, (hi : i ≤ n) →
      Submodule.span F (v '' {c : Fin n | (c : ℕ) < i}) = V ⟨i, by omega⟩ := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 : V ⟨0, by omega⟩ = ⊥ := Submodule.finrank_eq_zero.mp (hV.2 _)
      rw [h0, Submodule.span_eq_bot]
      rintro _ ⟨c, hc, rfl⟩
      exact absurd hc (Nat.not_lt_zero _)
    | succ i ih =>
      intro hi
      have hset : v '' {c : Fin n | (c : ℕ) < i + 1} =
          insert (v ⟨i, by omega⟩) (v '' {c : Fin n | (c : ℕ) < i}) := by
        rw [← Set.image_insert_eq]
        congr 1
        ext c
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      have hle : V ⟨i, by omega⟩ ≤ V ⟨i + 1, by omega⟩ := hV.1 (by rw [Fin.mk_le_mk]; omega)
      have hvi : v ⟨i, by omega⟩ ∈ V ⟨i + 1, by omega⟩ := hvV ⟨i, by omega⟩
      have hvi' : v ⟨i, by omega⟩ ∉ V ⟨i, by omega⟩ := hvnot ⟨i, by omega⟩
      rw [hset, Submodule.span_insert, ih (by omega)]
      apply Submodule.eq_of_le_of_finrank_eq
      · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hvi) hle
      · have hlt' : V ⟨i, by omega⟩ < F ∙ v ⟨i, by omega⟩ ⊔ V ⟨i, by omega⟩ :=
          lt_of_le_of_ne le_sup_right fun h => hvi' (h ▸ Submodule.mem_sup_left
            (Submodule.mem_span_singleton_self _))
        have h1 := Submodule.finrank_lt_finrank_of_lt hlt'
        have h2 := Submodule.finrank_mono (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
          hvi) hle)
        rw [hV.2] at h1 h2 ⊢
        simp only at h1 h2 ⊢
        omega
  set A : Matrix (Fin n) (Fin n) F := Matrix.of fun r c => v c r with hA
  have hAσ : A.map σ = A := by
    ext r c
    exact congrFun (hvfix c) r
  have hAcol : ∀ c, A *ᵥ Pi.single c 1 = v c := fun c => by
    rw [mulVec_single_one]
    rfl
  have hAmap : ∀ i : ℕ, (hi : i ≤ n) →
      (flagSpace n F i).map (mulVecLin A) = V ⟨i, by omega⟩ := fun i hi => by
    rw [flagSpace, Submodule.map_span, ← hspan i hi, ← Set.image_comp]
    congr 1
    ext w
    simp [hAcol]
  have hAunit : IsUnit A := by
    rw [← mulVec_surjective_iff_isUnit]
    intro w
    have htop : V ⟨n, by omega⟩ = ⊤ := Submodule.eq_top_of_finrank_eq (by
      rw [hV.2, finrank_fin_fun])
    have hw : w ∈ (flagSpace n F n).map (mulVecLin A) := by
      rw [hAmap n le_rfl, htop]
      exact Submodule.mem_top
    obtain ⟨u, -, hu⟩ := hw
    exact ⟨u, hu⟩
  have hd0 : A.det ≠ 0 := ((isUnit_iff_isUnit_det A).mp hAunit).ne_zero
  have hdσ : σ A.det = A.det := by
    rw [← RingEquiv.coe_toRingHom, RingHom.map_det, RingHom.mapMatrix_apply,
      RingEquiv.coe_toRingHom, hAσ]
  set e : Fin n → F := Pi.mulSingle ⟨0, hn⟩ A.det⁻¹ with he
  have he0 : ∀ i, e i ≠ 0 := fun i => by
    rw [he, Pi.mulSingle_apply]
    split_ifs
    · exact inv_ne_zero hd0
    · exact one_ne_zero
  have heσ : ∀ i, σ (e i) = e i := fun i => by
    rw [he, Pi.mulSingle_apply]
    split_ifs
    · rw [map_inv₀, hdσ]
    · exact map_one σ
  have hdet : (A * diagonal e).det = 1 := by
    rw [det_mul, det_diagonal, he, Fintype.prod_pi_mulSingle', mul_inv_cancel₀ hd0]
  refine ⟨⟨A * diagonal e, hdet⟩, ?_, fun i => ?_⟩
  · change (A * diagonal e).map σ = A * diagonal e
    rw [Matrix.map_mul, hAσ, diagonal_map (map_zero σ)]
    congr 2
    funext i
    exact heσ i
  · change (flagSpace n F i).map (mulVecLin (A * diagonal e)) = V i
    rw [mulVecLin_mul, Submodule.map_comp, map_diagonal_flagSpace he0, hAmap i (by omega)]

theorem comp_mem_flagSpace (τ : F ≃+* F) {i : ℕ} {v : Fin n → F} (hv : v ∈ flagSpace n F i) :
    ⇑τ ∘ v ∈ flagSpace n F i := by
  rw [mem_flagSpace] at hv ⊢
  intro j hj
  simp [hv j hj]

theorem coe_slMap (τ : F ≃+* F) (g : SpecialLinearGroup (Fin n) F) :
    ((SpecialLinearGroup.map τ.toRingHom g : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F).map τ := rfl

theorem slMap_mem_stabilizer_flagSpace (τ : F ≃+* F) {i : ℕ} {g : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ stabilizer (flagSpace n F i)) :
    SpecialLinearGroup.map τ.toRingHom g ∈ stabilizer (flagSpace n F i) := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨w, hw, rfl⟩
  have hu : ⇑τ.symm ∘ w ∈ flagSpace n F i := comp_mem_flagSpace τ.symm hw
  have hgu : (g : Matrix (Fin n) (Fin n) F) *ᵥ (⇑τ.symm ∘ w) ∈ flagSpace n F i := by
    rw [← mem_stabilizer.mp hg]
    exact ⟨_, hu, rfl⟩
  have h1 : w = ⇑τ ∘ (⇑τ.symm ∘ w) := by
    funext j
    simp
  rw [mulVecLin_apply, coe_slMap, h1, map_mulVec_comp]
  exact comp_mem_flagSpace τ hgu

theorem slMap_mem_flagStabilizer (τ : F ≃+* F) {I : Set ℕ} {g : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ flagStabilizer n F I) :
    SpecialLinearGroup.map τ.toRingHom g ∈ flagStabilizer n F I :=
  mem_flagStabilizer.mpr fun i hi =>
    slMap_mem_stabilizer_flagSpace τ (mem_flagStabilizer.mp hg i hi)

theorem map_mulVecLin_slMul (A B : SpecialLinearGroup (Fin n) F) (W : Submodule F (Fin n → F)) :
    W.map (mulVecLin ((A * B : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      (W.map (mulVecLin (B : Matrix (Fin n) (Fin n) F))).map
        (mulVecLin (A : Matrix (Fin n) (Fin n) F)) := by
  change W.map (mulVecLin ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F))) = _
  rw [mulVecLin_mul, Submodule.map_comp]

theorem map_mulVecLin_one (W : Submodule F (Fin n → F)) :
    W.map (mulVecLin ((1 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) = W := by
  change W.map (mulVecLin (1 : Matrix (Fin n) (Fin n) F)) = W
  rw [mulVecLin_one, Submodule.map_id]

theorem map_mulVecLin_inv_map (x : SpecialLinearGroup (Fin n) F) (W : Submodule F (Fin n → F)) :
    (W.map (mulVecLin (x : Matrix (Fin n) (Fin n) F))).map
      (mulVecLin ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) = W := by
  rw [← map_mulVecLin_slMul, inv_mul_cancel, map_mulVecLin_one]

theorem map_mulVecLin_map_inv (x : SpecialLinearGroup (Fin n) F) (W : Submodule F (Fin n → F)) :
    (W.map (mulVecLin ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F))).map
      (mulVecLin (x : Matrix (Fin n) (Fin n) F)) = W := by
  rw [← map_mulVecLin_slMul, mul_inv_cancel, map_mulVecLin_one]

theorem mem_stabilizer_map_iff {W : Submodule F (Fin n → F)}
    (x g : SpecialLinearGroup (Fin n) F) :
    g ∈ stabilizer (W.map (mulVecLin (x : Matrix (Fin n) (Fin n) F))) ↔
      x⁻¹ * g * x ∈ stabilizer W := by
  rw [mem_stabilizer, mem_stabilizer, map_mulVecLin_slMul, map_mulVecLin_slMul]
  constructor
  · intro h
    rw [h, map_mulVecLin_inv_map]
  · intro h
    have h2 := congrArg (Submodule.map (mulVecLin (x : Matrix (Fin n) (Fin n) F))) h
    rwa [map_mulVecLin_map_inv] at h2

theorem exists_fixed_flag_three [Finite F] {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {V₁ V₂ : Submodule F (Fin 3 → F)} (h12 : V₁ ≤ V₂) (h1 : finrank F V₁ = 1)
    (h2 : finrank F V₂ = 2) (hσ1 : ∀ v ∈ V₁, ⇑σ ∘ v ∈ V₁) (hσ2 : ∀ v ∈ V₂, ⇑σ ∘ v ∈ V₂) :
    ∃ z : SpecialLinearGroup (Fin 3) F, (z : Matrix (Fin 3) (Fin 3) F).map σ = z ∧
      (flagSpace 3 F 1).map (mulVecLin (z : Matrix (Fin 3) (Fin 3) F)) = V₁ ∧
      (flagSpace 3 F 2).map (mulVecLin (z : Matrix (Fin 3) (Fin 3) F)) = V₂ := by
  set V : Fin 4 → Submodule F (Fin 3 → F) := ![⊥, V₁, V₂, ⊤] with hV
  have hflag : IsCompleteFlag V := by
    refine ⟨Fin.monotone_iff_le_succ.mpr fun i => ?_, fun i => ?_⟩
    · fin_cases i
      · exact bot_le
      · exact h12
      · exact le_top
    · fin_cases i
      · exact finrank_bot F (Fin 3 → F)
      · exact h1
      · exact h2
      · change finrank F (⊤ : Submodule F (Fin 3 → F)) = 3
        rw [finrank_top, finrank_fin_fun]
  have hVσ : ∀ i, ∀ v ∈ V i, ⇑σ ∘ v ∈ V i := by
    intro i v hv
    fin_cases i
    · change v ∈ (⊥ : Submodule F (Fin 3 → F)) at hv
      rw [Submodule.mem_bot] at hv
      subst hv
      change _ ∈ (⊥ : Submodule F (Fin 3 → F))
      rw [Submodule.mem_bot]
      funext j
      simp
    · exact hσ1 v hv
    · exact hσ2 v hv
    · exact Submodule.mem_top
  obtain ⟨z, hz, hzV⟩ := exists_fixed_map_standardFlag_eq hσ hflag hVσ
  exact ⟨z, hz, hzV 1, hzV 2⟩

theorem slMap_slMap_symm (σ : F ≃+* F) (g : SpecialLinearGroup (Fin n) F) :
    SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map σ.symm.toRingHom g) = g := by
  ext i j
  change σ (σ.symm _) = _
  rw [RingEquiv.apply_symm_apply]

theorem exists_fixed_conj_le_of_parabolic [Finite F] [CharP F 2] {σ : F ≃+* F}
    (hσ : orderOf σ = 3) {P : Subgroup (SpecialLinearGroup (Fin 3) F)} (hP : IsProperParabolic P)
    (hPσ : ∀ p ∈ P, SpecialLinearGroup.map σ.toRingHom p ∈ P) :
    (∃ z : SpecialLinearGroup (Fin 3) F, (z : Matrix (Fin 3) (Fin 3) F).map σ = z ∧
      ∀ b ∈ upperTriangular 3 F, z * b * z⁻¹ ∈ P) ∧
    ∃ W : Submodule F (Fin 3 → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ p ∈ P, p ∈ stabilizer W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPtop, T, hT⟩ := hP
  obtain ⟨SU, hSU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) SU T
  have hxB : ∀ b ∈ upperTriangular 3 F, x * b * x⁻¹ ∈ P := by
    intro b hb
    apply hT
    have hTe : (T : Subgroup (SpecialLinearGroup (Fin 3) F)) =
        (unitriangular 3 F).map (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
          SpecialLinearGroup (Fin 3) F) := by
      rw [← hx, coe_sylow_smul, hSU]
    change x * b * x⁻¹ ∈ Subgroup.normalizer
      ((T : Subgroup (SpecialLinearGroup (Fin 3) F)) : Set (SpecialLinearGroup (Fin 3) F))
    rw [hTe, normalizer_map_conj, normalizer_unitriangular]
    exact ⟨b, hb, rfl⟩
  set P₀ := P.comap (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
    SpecialLinearGroup (Fin 3) F) with hP₀
  have hmemP₀ : ∀ q, q ∈ P₀ ↔ x * q * x⁻¹ ∈ P := fun q => Iff.rfl
  have hB : upperTriangular 3 F ≤ P₀ := fun b hb => (hmemP₀ b).mpr (hxB b hb)
  have hP₀top : P₀ ≠ ⊤ := by
    intro htop
    apply hPtop
    rw [eq_top_iff]
    intro s _
    have hs : x⁻¹ * s * x ∈ P₀ := by rw [htop]; exact Subgroup.mem_top _
    rw [hmemP₀] at hs
    simpa [mul_assoc] using hs
  set I := borelOvergroupCuts P₀ with hIdef
  have hQ : P₀ = flagStabilizer 3 F I := (borel_overgroups P₀ hB).1
  have hI3 : ∀ i ∈ I, 1 ≤ i ∧ i < 3 := fun i hi => by
    obtain ⟨hi1, hin, -⟩ := hi
    exact ⟨hi1, hin⟩
  have hIne : I.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hI
    apply hP₀top
    rw [hQ, hI, flagStabilizer_empty]
  set σx := SpecialLinearGroup.map σ.toRingHom x with hσx
  set y := x⁻¹ * σx with hy
  have hyP₀ : ∀ q ∈ P₀, y * q * y⁻¹ ∈ P₀ := by
    intro q hq
    rw [hmemP₀]
    have hq' : SpecialLinearGroup.map σ.symm.toRingHom q ∈ P₀ := by
      rw [hQ] at hq ⊢
      exact slMap_mem_flagStabilizer σ.symm hq
    have h1 := hPσ _ ((hmemP₀ _).mp hq')
    rw [map_mul, map_mul, map_inv, slMap_slMap_symm] at h1
    convert h1 using 1
    rw [hy, hσx]
    group
  have hcardP₀ : P₀.map (MulAut.conj y : SpecialLinearGroup (Fin 3) F →*
      SpecialLinearGroup (Fin 3) F) = P₀ :=
    Subgroup.eq_of_le_of_card_ge (fun _ ⟨q, hq, hqe⟩ => hqe ▸ hyP₀ q hq)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  have hyinv : ∀ q ∈ P₀, y⁻¹ * q * y ∈ P₀ := by
    intro q hq
    rw [← hcardP₀] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    simpa [mul_assoc] using hq'
  have hystab : ∀ i ∈ I, y ∈ stabilizer (flagSpace 3 F i) := by
    intro i hi
    have hinv : ∀ u ∈ unitriangular 3 F,
        ∀ v ∈ (flagSpace 3 F i).map (mulVecLin (y : Matrix (Fin 3) (Fin 3) F)),
          (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
            (flagSpace 3 F i).map (mulVecLin (y : Matrix (Fin 3) (Fin 3) F)) := by
      intro u hu v hv
      have hu' : y⁻¹ * u * y ∈ stabilizer (flagSpace 3 F i) := by
        have := hyinv u (hB (unitriangular_le_upperTriangular 3 F hu))
        rw [hQ] at this
        exact mem_flagStabilizer.mp this i hi
      have h2 := (mem_stabilizer_map_iff y u).mpr hu'
      rw [← mem_stabilizer.mp h2]
      exact ⟨v, hv, rfl⟩
    obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant hinv
    have hfin := congrArg (fun W : Submodule F (Fin 3 → F) => finrank F W) hW
    rw [show finrank F ((flagSpace 3 F i).map (mulVecLin (y : Matrix (Fin 3) (Fin 3) F))) =
      finrank F (flagSpace 3 F i) from LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' y) _,
      finrank_flagSpace (hI3 i hi).2.le, finrank_flagSpace hm] at hfin
    rw [mem_stabilizer, hW, hfin]
  have hxy : (x : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) =
      (x : Matrix (Fin 3) (Fin 3) F).map σ := by
    change ((x * y : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [hy, mul_inv_cancel_left]
    rfl
  have hWσ : ∀ i ∈ I, ∀ v ∈ (flagSpace 3 F i).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F)),
      ⇑σ ∘ v ∈ (flagSpace 3 F i).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F)) := by
    rintro i hi _ ⟨w, hw, rfl⟩
    have hyw : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ (⇑σ ∘ w) ∈ flagSpace 3 F i := by
      rw [← mem_stabilizer.mp (hystab i hi)]
      exact ⟨_, comp_mem_flagSpace σ hw, rfl⟩
    refine ⟨_, hyw, ?_⟩
    rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, hxy, map_mulVec_comp]
  set W₁ := (flagSpace 3 F 1).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F)) with hW₁def
  set W₂ := (flagSpace 3 F 2).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F)) with hW₂def
  have hW₁ : finrank F W₁ = 1 := by
    rw [hW₁def, show finrank F ((flagSpace 3 F 1).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F))) =
      finrank F (flagSpace 3 F 1) from LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' x) _,
      finrank_flagSpace (by norm_num)]
  have hW₂ : finrank F W₂ = 2 := by
    rw [hW₂def, show finrank F ((flagSpace 3 F 2).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F))) =
      finrank F (flagSpace 3 F 2) from LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' x) _,
      finrank_flagSpace (by norm_num)]
  have hW₁₂ : W₁ ≤ W₂ := Submodule.map_mono (flagSpace_mono (by norm_num))
  have hspanσ : ∀ v : Fin 3 → F, ⇑σ ∘ v = v → ∀ u ∈ F ∙ v, ⇑σ ∘ u ∈ F ∙ v := by
    intro v hvσ u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine Submodule.mem_span_singleton.mpr ⟨σ c, ?_⟩
    funext j
    have := congrFun hvσ j
    simp only [Function.comp_apply] at this
    simp [this]
  obtain ⟨V₁, V₂, h12, h1, h2, hσ1, hσ2, hV₁, hV₂⟩ : ∃ V₁ V₂ : Submodule F (Fin 3 → F),
      V₁ ≤ V₂ ∧ finrank F V₁ = 1 ∧ finrank F V₂ = 2 ∧ (∀ v ∈ V₁, ⇑σ ∘ v ∈ V₁) ∧
        (∀ v ∈ V₂, ⇑σ ∘ v ∈ V₂) ∧ (1 ∈ I → V₁ = W₁) ∧ (2 ∈ I → V₂ = W₂) := by
    by_cases hi1 : 1 ∈ I <;> by_cases hi2 : 2 ∈ I
    · exact ⟨W₁, W₂, hW₁₂, hW₁, hW₂, hWσ 1 hi1, hWσ 2 hi2, fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨v, -, hv, hvσ⟩ := exists_fixed_mem_not_le hσ (W := ⊤) (W' := W₁)
        (fun _ _ => Submodule.mem_top) (fun h => by
          have := Submodule.finrank_mono h
          rw [finrank_top, finrank_fin_fun, hW₁] at this
          omega)
      have hv0 : v ≠ 0 := fun h => hv (h ▸ W₁.zero_mem)
      refine ⟨W₁, W₁ ⊔ F ∙ v, le_sup_left, hW₁, ?_, hWσ 1 hi1, ?_, fun _ => rfl,
        fun h => absurd h hi2⟩
      · have hlt : W₁ < W₁ ⊔ F ∙ v := lt_of_le_of_ne le_sup_left fun h =>
          hv (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
        have hle := Submodule.finrank_add_le_finrank_add_finrank W₁ (F ∙ v)
        have hgt := Submodule.finrank_lt_finrank_of_lt hlt
        rw [finrank_span_singleton hv0, hW₁] at hle
        rw [hW₁] at hgt
        omega
      · intro u hu
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
        have hab : ⇑σ ∘ (a + b) = ⇑σ ∘ a + ⇑σ ∘ b := by
          funext j
          simp
        rw [hab]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hWσ 1 hi1 a ha))
          (Submodule.mem_sup_right (hspanσ v hvσ b hb))
    · obtain ⟨v, hvW, hv, hvσ⟩ := exists_fixed_mem_not_le hσ (W := W₂) (W' := ⊥) (hWσ 2 hi2)
        (fun h => by
          have := Submodule.finrank_mono h
          rw [finrank_bot, hW₂] at this
          omega)
      have hv0 : v ≠ 0 := fun h => hv (h ▸ Submodule.zero_mem _)
      exact ⟨F ∙ v, W₂, (Submodule.span_singleton_le_iff_mem _ _).mpr hvW,
        finrank_span_singleton hv0, hW₂, hspanσ v hvσ, hWσ 2 hi2, fun h => absurd h hi1,
        fun _ => rfl⟩
    · exfalso
      obtain ⟨i, hi⟩ := hIne
      obtain ⟨hi1', hi3⟩ := hI3 i hi
      interval_cases i
      · exact hi1 hi
      · exact hi2 hi
  obtain ⟨z, hz, hz1, hz2⟩ := exists_fixed_flag_three hσ h12 h1 h2 hσ1 hσ2
  refine ⟨⟨z, hz, fun b hb => ?_⟩, ?_⟩
  swap
  · obtain ⟨i, hi⟩ := hIne
    obtain ⟨hi1', hi3⟩ := hI3 i hi
    have hfin : finrank F ((flagSpace 3 F i).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F))) =
        i := by
      rw [show finrank F ((flagSpace 3 F i).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F))) =
        finrank F (flagSpace 3 F i) from LinearEquiv.finrank_map_eq
          (SpecialLinearGroup.toLin' x) _, finrank_flagSpace hi3.le]
    refine ⟨(flagSpace 3 F i).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F)), fun h => ?_,
      fun h => ?_, fun p hp => ?_⟩
    · rw [h, finrank_bot] at hfin
      omega
    · rw [h, finrank_top, finrank_fin_fun] at hfin
      omega
    · rw [mem_stabilizer_map_iff]
      have : x⁻¹ * p * x ∈ P₀ := by
        rw [hmemP₀]
        simpa [mul_assoc] using hp
      rw [hQ] at this
      exact mem_flagStabilizer.mp this i hi
  have hzb : x⁻¹ * (z * b * z⁻¹) * x ∈ P₀ := by
    rw [hQ, mem_flagStabilizer]
    intro i hi
    rw [← mem_stabilizer_map_iff]
    have hWi : (flagSpace 3 F i).map (mulVecLin (x : Matrix (Fin 3) (Fin 3) F)) =
        (flagSpace 3 F i).map (mulVecLin (z : Matrix (Fin 3) (Fin 3) F)) := by
      obtain ⟨hi1', hi3⟩ := hI3 i hi
      interval_cases i
      · rw [hz1, hV₁ hi]
      · rw [hz2, hV₂ hi]
    rw [hWi, mem_stabilizer_map_iff]
    have hb' := mem_flagStabilizer.mp (upperTriangular_le_flagStabilizer I hb) i hi
    simpa [mul_assoc] using hb'
  rw [hmemP₀] at hzb
  simpa [mul_assoc] using hzb

theorem eq_bot_or_eq_top_of_transvection {W : Submodule F (Fin 3 → F)}
    (hW : ∀ a b : Fin 3, a ≠ b → ∀ v ∈ W, transvection a b (1 : F) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  have hsingle : ∀ a b : Fin 3, a ≠ b → ∀ w ∈ W, (Pi.single a (w b) : Fin 3 → F) ∈ W := by
    intro a b hab w hw
    have h1 := hW a b hab w hw
    rw [transvection_mulVec, one_mul] at h1
    have := W.sub_mem h1 hw
    rwa [add_sub_cancel_left] at this
  have he : ∀ a : Fin 3, a ≠ j → (Pi.single a (1 : F) : Fin 3 → F) ∈ W := by
    intro a ha
    have h2 := W.smul_mem (v j)⁻¹ (hsingle a j ha v hv)
    rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hj] at h2
  have hall : ∀ a : Fin 3, (Pi.single a (1 : F) : Fin 3 → F) ∈ W := by
    intro a
    by_cases ha : a = j
    · subst ha
      obtain ⟨b, hb⟩ : ∃ b : Fin 3, b ≠ a := ⟨a + 1, by fin_cases a <;> decide⟩
      have h3 := hsingle a b (Ne.symm hb) _ (he b hb)
      simpa using h3
    · exact he a ha
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine W.sum_mem fun a _ => ?_
  have : (Pi.single a (w a) : Fin 3 → F) = w a • Pi.single a 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this]
  exact W.smul_mem _ (hall a)


end Flag

section Subfield

variable {K : Type} [Field K]

theorem scalars_le_ker_proj_comp (σ : K ≃+* K) :
    scalars 3 (fixedField σ) ≤
      ((proj 3 K).comp (SpecialLinearGroup.map (fixedField σ).subtype)).ker := by
  rintro A ⟨c, hc, hA⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff]
  refine ⟨Units.map (fixedField σ).subtype.toMonoidHom c, by rw [← map_pow, hc, map_one], ?_⟩
  change (A : Matrix (Fin 3) (Fin 3) (fixedField σ)).map (fixedField σ).subtype = _
  rw [hA]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [scalar_apply, diagonal_apply_ne _ hij]

@[expose] noncomputable def subfieldProj (σ : K ≃+* K) :
    projectiveSL 3 (fixedField σ) →* projectiveSL 3 K :=
  QuotientGroup.lift (scalars 3 (fixedField σ))
    ((proj 3 K).comp (SpecialLinearGroup.map (fixedField σ).subtype))
    (scalars_le_ker_proj_comp σ)

theorem subfieldProj_proj (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 3) (fixedField σ)) :
    subfieldProj σ (proj 3 (fixedField σ) A) =
      proj 3 K (SpecialLinearGroup.map (fixedField σ).subtype A) :=
  rfl

theorem slMap_transvection_one (σ : K ≃+* K) {a b : Fin 3} (hab : a ≠ b) :
    ((SpecialLinearGroup.map (fixedField σ).subtype
      (SpecialLinearGroup.transvection hab (1 : fixedField σ)) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = transvection a b (1 : K) := by
  ext i j
  change (fixedField σ).subtype (transvection a b (1 : fixedField σ) i j) = _
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem isProperParabolic_comap_subfieldProj [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {P : Subgroup (projectiveSL 3 K)}
    (hP : IsProperParabolic P)
    (hPσ : ∀ y ∈ P, fieldAut 3 K σ y ∈ P) :
    IsProperParabolic (P.comap (subfieldProj σ)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F₀ := fixedField σ with hF₀
  set Ph := P.comap (proj 3 K) with hPh
  have hPh' := isProperParabolic_comap (proj 3 K) (proj_surjective 3 K) hP
  have hPhσ : ∀ p ∈ Ph, SpecialLinearGroup.map σ.toRingHom p ∈ Ph := by
    intro p hp
    change proj 3 K (SpecialLinearGroup.map σ.toRingHom p) ∈ P
    rw [← fieldAut_proj]
    exact hPσ _ hp
  obtain ⟨⟨z, hz, hzB⟩, W, hW0, hWtop, hWstab⟩ :=
    exists_fixed_conj_le_of_parabolic hσ hPh' hPhσ
  obtain ⟨z₀, hz₀⟩ := CFSG.RankThree.PartTwo.KFacts.exists_sl_map_subtype_eq (σ := σ) (A := z)
    (Subtype.ext hz)
  set Q := P.comap (subfieldProj σ) with hQ
  have hQB : ∀ b ∈ upperTriangular 3 F₀,
      proj 3 F₀ z₀ * proj 3 F₀ b * (proj 3 F₀ z₀)⁻¹ ∈ Q := by
    intro b hb
    have e1 : proj 3 F₀ z₀ * proj 3 F₀ b * (proj 3 F₀ z₀)⁻¹ = proj 3 F₀ (z₀ * b * z₀⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    have e2 : SpecialLinearGroup.map F₀.subtype (z₀ * b * z₀⁻¹) =
        z * SpecialLinearGroup.map F₀.subtype b * z⁻¹ := by
      rw [map_mul, map_mul, map_inv, hz₀]
    change subfieldProj σ _ ∈ P
    rw [e1, subfieldProj_proj, e2]
    refine hzB _ fun i j hij => ?_
    change (F₀.subtype ((b : Matrix (Fin 3) (Fin 3) F₀) i j)) = 0
    rw [hb i j hij, map_zero]
  refine ⟨fun htop => ?_, ?_⟩
  ·
    have hall : ∀ a b : Fin 3, a ≠ b → ∀ v ∈ W, transvection a b (1 : K) *ᵥ v ∈ W := by
      intro a b hab v hv
      have hmem : proj 3 F₀ (SpecialLinearGroup.transvection hab (1 : F₀)) ∈ Q :=
        htop ▸ Subgroup.mem_top _
      have hst := hWstab _ hmem
      rw [← slMap_transvection_one σ hab, ← mem_stabilizer.mp hst]
      exact ⟨v, hv, rfl⟩
    rcases eq_bot_or_eq_top_of_transvection hall with h | h
    · exact hW0 h
    · exact hWtop h
  · obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := F₀) 2 (n := 3) (by norm_num)
    refine ⟨proj 3 F₀ z₀ • SU, fun y hy => ?_⟩
    rw [coe_sylow_smul, hSU, normalizer_map_conj, normalizer_projUnitriangular 2] at hy
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hy
    exact hQB b hb

end Subfield


end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof
