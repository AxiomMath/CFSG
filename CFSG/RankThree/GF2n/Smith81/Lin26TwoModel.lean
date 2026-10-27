module

public import CFSG.RankThree.GF2n.Smith81.Lin26Scalar

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

section Two

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {V₁ V₂ : Subgroup G}

theorem TensorModel.exists_lgen_phi_eq (TM : TensorModel M Q Z B)
    (g : Matrix (Fin 2) (Fin 2) TM.F) (hg : g.det = 1) :
    ∃ s : ↥(Lgen M (LB M Q B)), (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) = g := by
  have hmem : Matrix.GeneralLinearGroup.mkOfDetNeZero g (by rw [hg]; exact one_ne_zero) ∈
      TM.φ.range := by
    rw [TM.φ_range]
    exact StatedAPI.mem_statedSL_iff.mpr (by simpa using hg)
  obtain ⟨s, hs⟩ := hmem
  exact ⟨s, by rw [hs]; rfl⟩

theorem TensorModel.exists_plane_of_module (hc : Ctx M Q Z B) (TM : TensorModel M Q Z B)
    {V : Subgroup G} (hZV : Z ≤ V) (hVQ : V ≤ Q)
    (hN : Lgen M (LB M Q B) ≤ Subgroup.normalizer (V : Set G))
    (hcard : Nat.card V = Nat.card Z ^ 3) :
    ∃ u : Fin 2 → TM.F, u ≠ 0 ∧ ∀ e, e ∈ TM.M₀.img V ↔ TM.Φ e ∈ planeAdd u := by
  let Y : AddSubgroup (Matrix (Fin 2) (Fin 2) TM.F) :=
    (TM.M₀.img V).map TM.Φ.toAddMonoidHom
  have hYmem : ∀ X, X ∈ Y ↔ TM.Φ.symm X ∈ TM.M₀.img V := by
    intro X
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa using he
    · intro h
      exact ⟨_, h, by simp⟩
  have hY : ∀ g : Matrix (Fin 2) (Fin 2) TM.F, g.det = 1 → ∀ X ∈ Y, g * X ∈ Y := by
    intro g hg X hX
    obtain ⟨s, hs⟩ := TensorModel.exists_lgen_phi_eq TM g hg
    rw [hYmem] at hX ⊢
    obtain ⟨v, hvV, hvQ, hv⟩ := hX
    have hsv : (s : G) * v * (s : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hN s.2) v).mp hvV
    have hsvQ : (s : G) * v * (s : G)⁻¹ ∈ Q := TM.conj_mem_Q s.2 hvQ
    refine ⟨_, hsv, hsvQ, ?_⟩
    apply TM.Φ.injective
    rw [AddEquiv.apply_symm_apply, TM.act s v hvQ, hs, hv, AddEquiv.apply_symm_apply]
  have hYcard : Nat.card Y = Nat.card TM.F ^ 2 := by
    have h1 : Nat.card Y = Nat.card (TM.M₀.img V) :=
      Nat.card_congr (TM.Φ.toEquiv.subtypeEquiv fun e => by
        constructor
        · intro he; exact ⟨e, he, rfl⟩
        · rintro ⟨e', he', h⟩
          have : e' = e := TM.Φ.injective h
          rwa [this] at he')|>.symm
    have h2 := TM.M₀.card_eq hVQ hZV
    rw [hcard] at h2
    have hz : 0 < Nat.card Z := Nat.card_pos
    have h3 : Nat.card (TM.M₀.img V) = Nat.card Z ^ 2 := by
      have : Nat.card Z * Nat.card (TM.M₀.img V) = Nat.card Z * Nat.card Z ^ 2 := by
        rw [← h2]; ring
      exact Nat.eq_of_mul_eq_mul_left hz this
    rw [h1, h3, TM.card_F]
  obtain ⟨u, hu, hYu⟩ := eq_planeAdd_of_card Y hY hYcard
  refine ⟨u, hu, fun e => ?_⟩
  rw [← hYu]
  constructor
  · intro he; exact ⟨e, he, rfl⟩
  · rintro ⟨e', he', h⟩
    have : e' = e := TM.Φ.injective h
    rwa [this] at he'

private theorem TensorModel.exists_coord {TM : TensorModel M Q Z B} {u : Fin 2 → TM.F}
    (hu : u ≠ 0) (W : Submodule TM.K TM.M₀.E) (hW : ∀ e, e ∈ W ↔ TM.Φ e ∈ planeAdd u) :
    ∃ ψ : ↥W ≃+ (Fin 2 → TM.F), (∀ (c : TM.K) (w : ↥W), ψ (c • w) = TM.ε c • ψ w) ∧
      ∀ w : ↥W, TM.Φ (w : TM.M₀.E) = Matrix.vecMulVec (ψ w) u := by
  let toP : ↥W ≃+ planeAdd u :=
    { toFun := fun w => ⟨TM.Φ (w : TM.M₀.E), (hW _).mp w.2⟩
      invFun := fun X => ⟨TM.Φ.symm (X : Matrix (Fin 2) (Fin 2) TM.F),
        (hW _).mpr (by rw [AddEquiv.apply_symm_apply]; exact X.2)⟩
      left_inv := fun w => Subtype.ext (TM.Φ.symm_apply_apply _)
      right_inv := fun X => Subtype.ext (TM.Φ.apply_symm_apply _)
      map_add' := fun a b => Subtype.ext (map_add TM.Φ (a : TM.M₀.E) (b : TM.M₀.E)) }
  have hcoe : ∀ X : planeAdd u, Matrix.vecMulVec ((planeEquiv hu).symm X) u =
      (X : Matrix (Fin 2) (Fin 2) TM.F) := fun X => by
    rw [← coe_planeEquiv hu, AddEquiv.apply_symm_apply]
  refine ⟨toP.trans (planeEquiv hu).symm, fun c w => ?_, fun w => ?_⟩
  · rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_planeEquiv, Matrix.smul_vecMulVec, hcoe]
    show TM.Φ (c • (w : TM.M₀.E)) = TM.ε c • TM.Φ (w : TM.M₀.E)
    exact TM.smul c _
  · rw [AddEquiv.trans_apply, hcoe]
    rfl

theorem TensorModel.exists_lift (TM : TensorModel M Q Z B) {u₁ u₂ : Fin 2 → TM.F}
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hne : ∀ c : TM.F, u₂ ≠ c • u₁)
    (W₁ W₂ : Submodule TM.K TM.M₀.E) (hW₁ : ∀ e, e ∈ W₁ ↔ TM.Φ e ∈ planeAdd u₁)
    (hW₂ : ∀ e, e ∈ W₂ ↔ TM.Φ e ∈ planeAdd u₂) (hsup : W₁ ⊔ W₂ = ⊤)
    (U : TM.M₀.E →ₗ[TM.K] TM.M₀.E) (hUQ : ∀ e, TM.M₀.Qf (U e) = TM.M₀.Qf e)
    (h₁ : ∀ w ∈ W₁, U w ∈ W₁) (h₂ : ∀ w ∈ W₂, U w ∈ W₂)
    (hdet : LinearMap.det (U.restrict h₁) = 1) :
    ∃ s : ↥(Lgen M (LB M Q B)),
      ∀ e, TM.Φ (U e) = (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) * TM.Φ e := by
  obtain ⟨ψ₁, hψ₁s, hψ₁⟩ := TensorModel.exists_coord hu₁ W₁ hW₁
  obtain ⟨ψ₂, hψ₂s, hψ₂⟩ := TensorModel.exists_coord hu₂ W₂ hW₂
  obtain ⟨A₁, hA₁v, hA₁d⟩ := exists_matrix_det_eq TM.ε ψ₁ hψ₁s (U.restrict h₁)
  obtain ⟨A₂, hA₂v, -⟩ := exists_matrix_det_eq TM.ε ψ₂ hψ₂s (U.restrict h₂)
  rw [hdet, map_one] at hA₁d
  have hU₁ : ∀ w : ↥W₁, TM.Φ (U (w : TM.M₀.E)) = Matrix.vecMulVec (A₁.mulVec (ψ₁ w)) u₁ := by
    intro w
    have h := hψ₁ ⟨U (w : TM.M₀.E), h₁ w w.2⟩
    rw [← hA₁v w] at *
    exact h
  have hU₂ : ∀ w : ↥W₂, TM.Φ (U (w : TM.M₀.E)) = Matrix.vecMulVec (A₂.mulVec (ψ₂ w)) u₂ := by
    intro w
    have h := hψ₂ ⟨U (w : TM.M₀.E), h₂ w w.2⟩
    rw [← hA₂v w] at *
    exact h
  have hd : u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0 ≠ 0 := det_ne_zero_of_ne_smul hu₁ hne
  have hcross : ∀ n₁ n₂ : Fin 2 → TM.F,
      (A₁.mulVec n₁) 0 * (A₂.mulVec n₂) 1 - (A₁.mulVec n₁) 1 * (A₂.mulVec n₂) 0 =
        n₁ 0 * n₂ 1 - n₁ 1 * n₂ 0 := by
    intro n₁ n₂
    set w₁ : ↥W₁ := ψ₁.symm n₁ with hw₁
    set w₂ : ↥W₂ := ψ₂.symm n₂ with hw₂
    have h1 : ψ₁ w₁ = n₁ := ψ₁.apply_symm_apply n₁
    have h2 : ψ₂ w₂ = n₂ := ψ₂.apply_symm_apply n₂
    have hq := hUQ ((w₁ : TM.M₀.E) + (w₂ : TM.M₀.E))
    have hq' := congrArg TM.ε hq
    rw [TM.qf, TM.qf] at hq'
    simp only [map_add] at hq'
    rw [hU₁ w₁, hU₂ w₂, hψ₁ w₁, hψ₂ w₂, h1, h2, det_vecMulVec_add, det_vecMulVec_add] at hq'
    exact mul_right_cancel₀ hd hq'
  have hA : A₂ = A₁ := by
    have hdet1 : A₁ 0 0 * A₁ 1 1 - A₁ 0 1 * A₁ 1 0 = 1 := by
      have := hA₁d
      rwa [Matrix.det_fin_two] at this
    have e00 := hcross (Pi.single 0 1) (Pi.single 0 1)
    have e01 := hcross (Pi.single 0 1) (Pi.single 1 1)
    have e10 := hcross (Pi.single 1 1) (Pi.single 0 1)
    have e11 := hcross (Pi.single 1 1) (Pi.single 1 1)
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]
      linear_combination (A₁ 0 1) * e00 - (A₁ 0 0) * e10 - (A₂ 0 0) * hdet1
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
      linear_combination (A₁ 0 1) * e01 - (A₁ 0 0) * e11 - (A₂ 0 1) * hdet1
    · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue]
      linear_combination (A₁ 1 1) * e00 - (A₁ 1 0) * e10 - (A₂ 1 0) * hdet1
    · simp only [Fin.mk_one, Fin.isValue]
      linear_combination (A₁ 1 1) * e01 - (A₁ 1 0) * e11 - (A₂ 1 1) * hdet1
  obtain ⟨s, hs⟩ := TensorModel.exists_lgen_phi_eq TM A₁ hA₁d
  refine ⟨s, fun e => ?_⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
    (show e ∈ W₁ ⊔ W₂ by rw [hsup]; exact Submodule.mem_top)
  rw [hs, map_add, map_add, map_add, hU₁ ⟨w₁, hw₁⟩, hU₂ ⟨w₂, hw₂⟩, hψ₁ ⟨w₁, hw₁⟩, hψ₂ ⟨w₂, hw₂⟩,
    Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hA]

theorem exists_restModel_sl_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) :
    ∃ R : RestModel M Q Z 2 V₁ V₂, R.SLProp := by
  classical
  obtain ⟨TM⟩ := exists_tensorModel hc hS
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hN₁, hN₂, hc₁, hc₂⟩ := hS.basic
  have hsumQ := LinSetup.exists_mul hc.hyp hS
  obtain ⟨φ, hφπ, hφker, hφQf⟩ := exists_actionHom_H0 hc.hyp TM.gm
  obtain ⟨u₁, hu₁, hP₁⟩ := TM.exists_plane_of_module hc hZV₁ hV₁Q hN₁ hc₁
  obtain ⟨u₂, hu₂, hP₂⟩ := TM.exists_plane_of_module hc hZV₂ hV₂Q hN₂ hc₂
  have hK₁ : ∀ (c : TM.K) {x : TM.M₀.E}, x ∈ TM.M₀.img V₁ → c • x ∈ TM.M₀.img V₁ := by
    intro c x hx
    rw [hP₁] at hx ⊢
    rw [TM.smul]
    exact smul_mem_planeAdd hx _
  have hK₂ : ∀ (c : TM.K) {x : TM.M₀.E}, x ∈ TM.M₀.img V₂ → c • x ∈ TM.M₀.img V₂ := by
    intro c x hx
    rw [hP₂] at hx ⊢
    rw [TM.smul]
    exact smul_mem_planeAdd hx _
  let W₁ : Submodule TM.K TM.M₀.E :=
    { carrier := (TM.M₀.img V₁ : Set TM.M₀.E)
      add_mem' := fun ha hb => (TM.M₀.img V₁).add_mem ha hb
      zero_mem' := (TM.M₀.img V₁).zero_mem
      smul_mem' := fun c _ hx => hK₁ c hx }
  let W₂ : Submodule TM.K TM.M₀.E :=
    { carrier := (TM.M₀.img V₂ : Set TM.M₀.E)
      add_mem' := fun ha hb => (TM.M₀.img V₂).add_mem ha hb
      zero_mem' := (TM.M₀.img V₂).zero_mem
      smul_mem' := fun c _ hx => hK₂ c hx }
  have hW₁mem : ∀ x : TM.M₀.E, x ∈ W₁ ↔ x ∈ TM.M₀.img V₁ := fun x => Iff.rfl
  have hW₂mem : ∀ x : TM.M₀.E, x ∈ W₂ ↔ x ∈ TM.M₀.img V₂ := fun x => Iff.rfl
  have hsumE : ∀ e : TM.M₀.E, ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, e = w₁ + w₂ := by
    intro e
    obtain ⟨q, hq, rfl⟩ := TM.M₀.π_surj e
    obtain ⟨a, ha, b', hb', rfl⟩ := hsumQ q hq
    exact ⟨TM.M₀.π a, (hW₁mem _).mpr (TM.M₀.pi_mem_img ha (hV₁Q ha)), TM.M₀.π b',
      (hW₂mem _).mpr (TM.M₀.pi_mem_img hb' (hV₂Q hb')), TM.M₀.π_mul a (hV₁Q ha) b' (hV₂Q hb')⟩
  have hcard1 : Nat.card ↥W₁ = Nat.card Z ^ 2 := by
    have h2 := TM.M₀.card_eq hV₁Q hZV₁
    rw [hc₁, pow_succ'] at h2
    have hz : 0 < Nat.card Z := Nat.card_pos
    have h3 : Nat.card ↥(TM.M₀.img V₁) = Nat.card Z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hz h2.symm
    rw [← h3]
    exact Nat.card_congr (Equiv.refl _)
  have hcard2 : Nat.card ↥W₂ = Nat.card Z ^ 2 := by
    have h2 := TM.M₀.card_eq hV₂Q hZV₂
    rw [hc₂, pow_succ'] at h2
    have hz : 0 < Nat.card Z := Nat.card_pos
    have h3 : Nat.card ↥(TM.M₀.img V₂) = Nat.card Z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hz h2.symm
    rw [← h3]
    exact Nat.card_congr (Equiv.refl _)
  have hiso : ∀ (u : Fin 2 → TM.F) (e e' : TM.M₀.E), TM.Φ e ∈ planeAdd u → TM.Φ e' ∈ planeAdd u →
      TM.M₀.B e e' = 0 := by
    intro u e e' he he'
    have h1 := congrArg TM.ε (TM.M₀.Qf_add e e')
    rw [map_add, map_add, TM.qf, TM.qf, TM.qf, map_add, det_add_of_mem_planeAdd he he'] at h1
    have h3 : TM.ε (TM.M₀.B e e') = 0 := by linear_combination -h1
    exact TM.ε.injective (h3.trans (map_zero TM.ε).symm)
  have hsupW : W₁ ⊔ W₂ = ⊤ := by
    rw [eq_top_iff]
    intro e _
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hsumE e
    exact Submodule.add_mem_sup hw₁ hw₂
  have hintW : W₁ ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨a, ha, haQ, rfl⟩ := (hW₁mem e).mp he.1
    have hb : TM.M₀.π a ∈ TM.M₀.img V₂ := (hW₂mem _).mp he.2
    have haV₂ : a ∈ V₂ := (TM.M₀.mem_img_iff hZV₂ haQ).mp hb
    have haZ : a ∈ Z := by rw [← hint]; exact ⟨ha, haV₂⟩
    rw [Submodule.mem_bot]
    exact (TM.M₀.π_ker a haQ).mpr haZ
  refine ⟨{ hyp := hc.hyp
            ZV₁ := hZV₁
            V₁Q := hV₁Q
            ZV₂ := hZV₂
            V₂Q := hV₂Q
            V₁₂ := hint
            dec := hsumQ
            K := TM.K
            γ := TM.γ
            M₀ := TM.M₀
            gm := TM.gm
            φ := φ
            φπ := hφπ
            φker := hφker
            φQf := hφQf
            W₁ := W₁
            W₂ := W₂
            memW₁ := hW₁mem
            memW₂ := hW₂mem
            hsup := hsupW
            hint := hintW
            iso₁ := fun e he e' he' => hiso u₁ e e' ((hP₁ e).mp he) ((hP₁ e').mp he')
            iso₂ := fun e he e' he' => hiso u₂ e e' ((hP₂ e).mp he) ((hP₂ e').mp he')
            card_W₁ := hcard1
            card_W₂ := hcard2 }, ?_⟩
  intro U hUQ h₁ h₂ hdet
  have hne : ∀ c : TM.F, u₂ ≠ c • u₁ := by
    intro c hc'
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hu₂ (by simpa using hc')
    have hpl : ∀ e, TM.Φ e ∈ planeAdd u₂ ↔ TM.Φ e ∈ planeAdd u₁ := fun e => by
      rw [hc', planeAdd_smul hc0]
    have hWW : ∀ e, e ∈ W₂ ↔ e ∈ W₁ := fun e => by
      rw [hW₂mem, hW₁mem, hP₂, hP₁, hpl]
    have hbot : W₁ = ⊥ := by
      rw [← hintW]
      ext e
      simp only [Submodule.mem_inf]
      exact ⟨fun h => ⟨h, (hWW e).mpr h⟩, fun h => h.1⟩
    have h1 : Nat.card ↥W₁ = 1 := by
      rw [hbot]
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    rw [hcard1] at h1
    have h4 := hc.hyp.q4
    have h5 : 1 < Nat.card Z ^ 2 := Nat.one_lt_pow two_ne_zero (by omega)
    omega
  obtain ⟨s, hs⟩ := TM.exists_lift hu₁ hu₂ hne W₁ W₂ hP₁ hP₂ hsupW U hUQ h₁ h₂ hdet
  refine ⟨(s : G), (Lgen_le_H0 hc s.2).1, fun x hx => ?_⟩
  apply TM.Φ.injective
  rw [TM.act s x hx, hs]

end Two

end CFSG.RankThree.GF2n.Smith81
