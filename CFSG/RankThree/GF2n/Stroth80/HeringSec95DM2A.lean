module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CTypeA
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Tensor

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.Quasithin.G11.P3Ortho.Om4 CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

section Algebra

variable {K Kn : Type} [Field K] [Field Kn]

theorem toMat_map (σ : Kn →+* K) (x : Fin 2 ⊕ Fin 2 → Kn) :
    toMat K (fun i => σ (x i)) = (toMat Kn x).map σ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat]

@[expose] def invT : SL(2, K) →* SL(2, K) where
  toFun g := ⟨((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ, by
    rw [Matrix.det_transpose]
    exact (g⁻¹).2⟩
  map_one' := by
    refine Subtype.ext ?_
    simp
  map_mul' g h := by
    refine Subtype.ext ?_
    simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    rfl

theorem coe_invT (g : SL(2, K)) :
    ((invT g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = ((g⁻¹ : SL(2, K)) : Matrix _ _ K)ᵀ := rfl

theorem invT_invT (g : SL(2, K)) : invT (invT g) = g := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_invT, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

end Algebra

section Helpers

variable {ι G Kg K' : Type} [Group G] [Field Kg] [Field K'] {Q Z V : Subgroup G} {γ : G → Kg}

theorem addEquiv_imgSub_smul' (M₀ : Tim79.QuadModel Q Z Kg γ) (hVQ : V ≤ Q)
    (hS : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V)
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K'))
    (θ : Kg ≃+* K')
    (hθ : ∀ (c : Kg) (v w : ↥V), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (Ψ : ↥(imgSub M₀ V hS) ≃+ (ι → K'))
    (hΨ : ∀ (v : ↥V) (h : M₀.π v ∈ imgSub M₀ V hS),
      Ψ ⟨M₀.π v, h⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∀ (c : Kg) (e : ↥(imgSub M₀ V hS)), Ψ (c • e) = θ c • Ψ e := by
  intro c e
  obtain ⟨v, hvV, hvQ, hv⟩ := M₀.mem_img.mp ((mem_imgSub (M₀ := M₀) (hS := hS)).mp e.2)
  obtain ⟨v', hv'V, hv'Q, hv'⟩ :=
    M₀.mem_img.mp (hS c _ ((mem_imgSub (M₀ := M₀) (hS := hS)).mpr (M₀.pi_mem_img hvV hvQ)))
  have hve : (e : M₀.E) = M₀.π v := hv.symm
  have hv'm : M₀.π v' = c • M₀.π v := by rw [hv']
  have hce : c • e = ⟨M₀.π v', (mem_imgSub (M₀ := M₀)).mpr
      (M₀.pi_mem_img hv'V hv'Q)⟩ := Subtype.ext (by
    show c • (e : M₀.E) = M₀.π v'
    rw [hve, ← hv'])
  have he : e = ⟨M₀.π v, (mem_imgSub (M₀ := M₀)).mpr
      (M₀.pi_mem_img hvV hvQ)⟩ := Subtype.ext hve
  calc
    Ψ (c • e) = Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v', hv'V⟩)) := by
      rw [hce]
      exact hΨ ⟨v', hv'V⟩ _
    _ = θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hvV⟩)) :=
      hθ c ⟨v, hvV⟩ ⟨v', hv'V⟩ hv'm
    _ = θ c • Ψ e := by
      rw [he]
      exact congrArg (θ c • ·) (hΨ ⟨v, hvV⟩ _).symm

@[expose] noncomputable def coordsEquiv' (M₀ : Tim79.QuadModel Q Z Kg γ)
    (hS : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V)
    (θ : Kg ≃+* K') (Ψ : ↥(imgSub M₀ V hS) ≃+ (ι → K'))
    (hΨsmul : ∀ (c : Kg) (e : ↥(imgSub M₀ V hS)), Ψ (c • e) = θ c • Ψ e) :
    ↥(imgSub M₀ V hS) ≃ₗ[Kg] (ι → Kg) :=
  AddEquiv.toLinearEquiv
    { toFun := fun e i => θ.symm (Ψ e i)
      invFun := fun v => Ψ.symm (fun i => θ (v i))
      left_inv := fun e => Ψ.injective (by
        rw [AddEquiv.apply_symm_apply]
        funext i
        exact RingEquiv.apply_symm_apply θ (Ψ e i))
      right_inv := fun v => by
        funext i
        change θ.symm (Ψ (Ψ.symm (fun i => θ (v i))) i) = v i
        rw [AddEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
      map_add' := fun e e' => by
        funext i
        change θ.symm (Ψ (e + e') i) = θ.symm (Ψ e i) + θ.symm (Ψ e' i)
        rw [map_add, Pi.add_apply, map_add] }
    fun c e => by
      funext i
      change θ.symm (Ψ (c • e) i) = c * θ.symm (Ψ e i)
      rw [hΨsmul, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]

end Helpers

section Coordinates

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure VDesc95 (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) where
  cV : M₀.E →ₗ[K] Matrix (Fin 2) (Fin 2) K
  ρ : ↥(Rt M (LB M Q B) t) →* (SL(2, K) × SL(2, K))
  cV_inj : ∀ e ∈ M₀.img (Vt M (LB M Q B) B Z t), cV e = 0 → e = 0
  cV_surj : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ e ∈ M₀.img (Vt M (LB M Q B) B Z t), cV e = X
  ρ_surj : Function.Surjective ρ
  cV_act : ∀ (r : ↥(Rt M (LB M Q B) t)) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
    cV (φ ⟨(r : G), hc.Rt_le_H0 t r.2⟩ e) =
      ((ρ r).1 : Matrix (Fin 2) (Fin 2) K) * cV e * ((ρ r).2 : Matrix (Fin 2) (Fin 2) K)ᵀ
  point : ∃ b : M₀.E, b ≠ 0 ∧ (∀ e, e ∈ M₀.img B ↔ ∃ c : K, e = c • b) ∧
    cV b = Matrix.single 0 0 1

theorem phi_mem_img_Vt {hc : Ctx M Q Z B} {t : G} (ht : t ∈ LB M Q B) {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {g : G} (hg : g ∈ Rt M (LB M Q B) t) {e : M₀.E}
    (he : e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    φ ⟨g, hc.Rt_le_H0 t hg⟩ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
  obtain ⟨x, hxV, hxQ, rfl⟩ := he
  rw [← hφπ _ x hxQ]
  have hx' : g * x * g⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hg) x).mp hxV
  exact M₀.pi_mem_img hx' (hc.Vt_le_Q t hx')

structure VDesc95Pre (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) where
  cV : M₀.E →ₗ[K] Matrix (Fin 2) (Fin 2) K
  ρ : ↥(Rt M (LB M Q B) t) →* (SL(2, K) × SL(2, K))
  cV_inj : ∀ e ∈ M₀.img (Vt M (LB M Q B) B Z t), cV e = 0 → e = 0
  cV_surj : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ e ∈ M₀.img (Vt M (LB M Q B) B Z t), cV e = X
  ρ_surj : Function.Surjective ρ
  cV_act : ∀ (r : ↥(Rt M (LB M Q B) t)) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
    cV (φ ⟨(r : G), hc.Rt_le_H0 t r.2⟩ e) =
      ((ρ r).1 : Matrix (Fin 2) (Fin 2) K) * cV e * ((ρ r).2 : Matrix (Fin 2) (Fin 2) K)ᵀ
  point : ∃ b : M₀.E, b ≠ 0 ∧ (∀ e, e ∈ M₀.img B ↔ ∃ c : K, e = c • b) ∧
    ∃ a a' : Fin 2 → K, a ≠ 0 ∧ a' ≠ 0 ∧ cV b = Matrix.vecMulVec a a'

theorem exists_vdescPre95 (h34 : Stroth34Statement) (hA : Sec9AExistsStatement) {n : ℕ}
    {hc : Ctx M Q Z B} {t : G} (hs : Sec9Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hglob : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    Nonempty (VDesc95Pre hc t M₀ φ) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨r0, hr0⟩ := hA G M Q Z B hc n t hs
  obtain ⟨Kn, fKn, finKn, chKn, hnorm, ⟨C⟩⟩ := exists_coord95 h34 hs hr0
  haveI := hnorm
  have hcardKn : Nat.card K = Nat.card Kn := hglob.card.trans C.hK.symm
  have hq4n : 4 ≤ Nat.card Kn := C.hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4n
  have hX := addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩
  set V := Vt M (LB M Q B) B Z t with hVdef
  have hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V := fun c e he =>
    hc.smul_mem_img_Vt hglob t c he
  have hlin : ∀ r ∈ Rt M (LB M Q B) t, ∃ T : M₀.E →ₗ[K] M₀.E,
      ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x) := fun r hr =>
    ⟨(φ ⟨r, hc.Rt_le_H0 t hr⟩ : M₀.E →ₗ[K] M₀.E),
      fun x hx => hφπ ⟨r, hc.Rt_le_H0 t hr⟩ x hx⟩
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcardKn M₀ (hc.Vt_le_Q t) hX hS hlin C.φ C.hφ
    (hc.Rt_normalizes_Vt ht) C.ψ C.hψ
  obtain ⟨Ψa, hΨa⟩ := exists_addEquiv_imgSub M₀ (hc.Vt_le_Q t) hS C.ψ
  have hΨsmul := addEquiv_imgSub_smul' M₀ (hc.Vt_le_Q t) hS C.ψ θ hθ Ψa hΨa
  let L := coordsEquiv' M₀ hS θ Ψa hΨsmul
  have hrange : ((Ψ Kn).toMonoidHom.comp C.φ).range = (rho' Kn).range := by
    have h1 : ((Ψ Kn).toMonoidHom.comp C.φ).range = C.φ.range.map (Ψ Kn).toMonoidHom :=
      MonoidHom.range_comp _ _
    rw [h1, C.hφ, map_statedOmega, commutator_eq_range hq4n]
  let ρn : ↥(Rt M (LB M Q B) t) →* SL(2, Kn) × SL(2, Kn) :=
    ((MonoidHom.ofInjective (rho'_injective (K := Kn))).symm.toMonoidHom).comp
      ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp
        ((Ψ Kn).toMonoidHom.comp C.φ).rangeRestrict)
  have hρn : ∀ g, rho' Kn (ρn g) = Ψ Kn (C.φ g) := by
    intro g
    have h := MonoidHom.apply_ofInjective_symm (rho'_injective (K := Kn))
      ((MulEquiv.subgroupCongr hrange)
        (((Ψ Kn).toMonoidHom.comp C.φ).rangeRestrict g))
    exact h
  have hρnsurj : Function.Surjective ρn := by
    intro z
    have hz : rho' Kn z ∈ ((Ψ Kn).toMonoidHom.comp C.φ).range := by
      rw [hrange]
      exact ⟨z, rfl⟩
    obtain ⟨g, hg⟩ := hz
    refine ⟨g, rho'_injective (K := Kn) ?_⟩
    rw [hρn g]
    exact hg
  let σ : Kn →+* K := θ.symm.toRingHom
  let τ : K →+* Kn := θ.toRingHom
  have hστ : ∀ x : K, σ (τ x) = x := fun x => θ.symm_apply_apply x
  have hτσ : ∀ x : Kn, τ (σ x) = x := fun x => θ.apply_symm_apply x
  have hmapστ : ∀ u : SL(2, K), Matrix.SpecialLinearGroup.map σ
      (Matrix.SpecialLinearGroup.map τ u) = u := by
    intro u
    refine Subtype.ext ?_
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hστ]
  let ρ : ↥(Rt M (LB M Q B) t) →* SL(2, K) × SL(2, K) :=
    (MonoidHom.prod ((Matrix.SpecialLinearGroup.map σ).comp (MonoidHom.fst _ _))
      (invT.comp ((Matrix.SpecialLinearGroup.map σ).comp (MonoidHom.snd _ _)))).comp ρn
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨u, v⟩
    obtain ⟨g, hg⟩ := hρnsurj (Matrix.SpecialLinearGroup.map τ u,
      Matrix.SpecialLinearGroup.map τ (invT v))
    refine ⟨g, ?_⟩
    simp only [ρ, MonoidHom.comp_apply, hg, MonoidHom.prod_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd, hmapστ, invT_invT]
  let c0 : ↥(imgSub M₀ V hS) →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
    (toMat K).toLinearMap ∘ₗ L.toLinearMap
  have hc0 : ∀ e : ↥(imgSub M₀ V hS), c0 e = (toMat Kn (Ψa e)).map σ := by
    intro e
    show toMat K (L e) = _
    rw [← toMat_map σ]
    rfl
  obtain ⟨Wc, hWc⟩ := Submodule.exists_isCompl (imgSub M₀ V hS)
  let P := (imgSub M₀ V hS).linearProjOfIsCompl Wc hWc
  let cV : M₀.E →ₗ[K] Matrix (Fin 2) (Fin 2) K := c0 ∘ₗ P
  have hcV : ∀ e (he : e ∈ M₀.img V), cV e = c0 ⟨e, he⟩ := by
    intro e he
    have hPe : P e = ⟨e, he⟩ := Submodule.linearProjOfIsCompl_apply_left hWc ⟨e, he⟩
    show c0 (P e) = _
    rw [hPe]
  have hinj : ∀ e ∈ M₀.img V, cV e = 0 → e = 0 := by
    intro e he h0
    rw [hcV e he] at h0
    have h1 : (⟨e, he⟩ : ↥(imgSub M₀ V hS)) = 0 := by
      apply L.injective
      apply (toMat K).injective
      simpa [c0] using h0
    exact congrArg Subtype.val h1
  have hsurj : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ e ∈ M₀.img V, cV e = X := by
    intro X
    refine ⟨((L.symm ((toMat K).symm X) : ↥(imgSub M₀ V hS)) : M₀.E),
      (L.symm ((toMat K).symm X)).2, ?_⟩
    rw [hcV _ (L.symm ((toMat K).symm X)).2]
    simp [c0]
  have hΨact : ∀ (g : ↥(Rt M (LB M Q B) t)) (e : ↥(imgSub M₀ V hS)),
      Ψa ⟨φ ⟨(g : G), hc.Rt_le_H0 t g.2⟩ e, phi_mem_img_Vt (hc := hc) ht φ hφπ g.2 e.2⟩ =
        (C.φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Kn) *ᵥ Ψa e := by
    intro g e
    obtain ⟨v, hvV, hvQ, hv⟩ := M₀.mem_img.mp ((mem_imgSub (M₀ := M₀) (hS := hS)).mp e.2)
    have hgM : (g : G) ∈ M := hc.Rt_le_M t g.2
    have hwV : (g : G) * v * (g : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht g.2) v).mp hvV
    have hwQ : (g : G) * v * (g : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) v).mp hvQ
    have he : e = ⟨M₀.π v, (mem_imgSub (M₀ := M₀) (hS := hS)).mpr
        (M₀.pi_mem_img hvV hvQ)⟩ := Subtype.ext hv.symm
    have heφ : (⟨φ ⟨(g : G), hc.Rt_le_H0 t g.2⟩ e, phi_mem_img_Vt (hc := hc) ht φ hφπ g.2 e.2⟩ :
        ↥(imgSub M₀ V hS)) = ⟨M₀.π ((g : G) * v * (g : G)⁻¹),
          (mem_imgSub (M₀ := M₀) (hS := hS)).mpr (M₀.pi_mem_img hwV hwQ)⟩ := Subtype.ext (by
      show φ ⟨(g : G), hc.Rt_le_H0 t g.2⟩ (e : M₀.E) = M₀.π ((g : G) * v * (g : G)⁻¹)
      rw [← hv, ← hφπ ⟨(g : G), hc.Rt_le_H0 t g.2⟩ v hvQ])
    rw [heφ, hΨa ⟨(g : G) * v * (g : G)⁻¹, hwV⟩, he, hΨa ⟨v, hvV⟩]
    exact C.hψ g ⟨v, hvV⟩ ⟨(g : G) * v * (g : G)⁻¹, hwV⟩ rfl
  have hc0act : ∀ (g : ↥(Rt M (LB M Q B) t)) (e : ↥(imgSub M₀ V hS)),
      c0 ⟨φ ⟨(g : G), hc.Rt_le_H0 t g.2⟩ e,
        phi_mem_img_Vt (hc := hc) ht φ hφπ g.2 e.2⟩ =
        ((ρ g).1 : Matrix (Fin 2) (Fin 2) K) * c0 e * ((ρ g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro g e
    rw [hc0, hc0, hΨact g e]
    have h1 : toMat Kn ((C.φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Kn) *ᵥ Ψa e) =
        Ψ Kn (C.φ g) (toMat Kn (Ψa e)) := by
      rw [Ψ_apply, LinearEquiv.symm_apply_apply]
    rw [h1, ← hρn g]
    have h2 : ∀ X, rho' Kn (ρn g) X = ((ρn g).1 : Matrix (Fin 2) (Fin 2) Kn) * X *
        (((ρn g).2⁻¹ : SL(2, Kn)) : Matrix (Fin 2) (Fin 2) Kn) := fun X =>
      specialRho_apply (ρn g) X
    rw [h2, Matrix.map_mul, Matrix.map_mul]
    have h3 : ((ρ g).1 : Matrix (Fin 2) (Fin 2) K) = ((ρn g).1 : Matrix (Fin 2) (Fin 2) Kn).map σ :=
      rfl
    have h4 : ((ρ g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ =
        (((ρn g).2⁻¹ : SL(2, Kn)) : Matrix (Fin 2) (Fin 2) Kn).map σ := by
      show (((invT (Matrix.SpecialLinearGroup.map σ (ρn g).2) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K))ᵀ = _
      rw [coe_invT, Matrix.transpose_transpose,
        ← (Matrix.SpecialLinearGroup.map σ).map_inv ((ρn g).2)]
      rfl
    rw [h3, h4]
  have hdet : (toMat Kn C.u).det = 0 := by
    rw [det_toMat]
    exact (congrFun (coe_quadPlus 2 Kn) C.u).symm.trans C.hQu
  have hu0' : toMat Kn C.u ≠ 0 := fun h =>
    C.hu0 ((toMat Kn).injective (by rw [h, map_zero]))
  obtain ⟨a, a', ha, ha', hrank⟩ := exists_vecMulVec_of_det_eq_zero hdet hu0'
  let e₀ : ↥(imgSub M₀ V hS) := Ψa.symm C.u
  have hΨe₀ : Ψa e₀ = C.u := Ψa.apply_symm_apply _
  have hBline : ∀ e, e ∈ M₀.img B ↔ ∃ c : K, e = c • (e₀ : M₀.E) := by
    intro e
    constructor
    · rintro ⟨x, hxB, hxQ, rfl⟩
      have hxV : x ∈ V := hc.B_le_Vt ht hxB
      have hmem : M₀.π x ∈ imgSub M₀ V hS := M₀.pi_mem_img hxV hxQ
      obtain ⟨c, hc'⟩ := (C.hBiff (secVec C.ψ ⟨x, hxV⟩)).mp ⟨⟨x, hxV⟩, hxB, rfl⟩
      refine ⟨θ.symm c, ?_⟩
      have h1 : Ψa ⟨M₀.π x, hmem⟩ = Ψa (θ.symm c • e₀) := by
        rw [hΨa ⟨x, hxV⟩ hmem, hΨsmul, hΨe₀, θ.apply_symm_apply]
        exact hc'
      exact congrArg Subtype.val (Ψa.injective h1)
    · rintro ⟨c, rfl⟩
      obtain ⟨b, hbB, hb⟩ := (C.hBiff (θ c • C.u)).mpr ⟨θ c, rfl⟩
      have hbV : (b : G) ∈ V := b.2
      have hbQ : (b : G) ∈ Q := hc.Vt_le_Q t hbV
      have hmem : M₀.π (b : G) ∈ imgSub M₀ V hS := M₀.pi_mem_img hbV hbQ
      have h1 : Ψa ⟨M₀.π (b : G), hmem⟩ = Ψa (c • e₀) := by
        rw [hΨa b hmem, hΨsmul, hΨe₀]
        exact hb
      have h2 := congrArg Subtype.val (Ψa.injective h1)
      exact ⟨b, hbB, hbQ, h2⟩
  have hcVe₀ : cV (e₀ : M₀.E) = Matrix.vecMulVec (fun i => σ (a i)) (fun i => σ (a' i)) := by
    rw [hcV _ e₀.2, hc0, hΨe₀, hrank]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have hσinj : ∀ v : Fin 2 → Kn, v ≠ 0 → (fun i => σ (v i)) ≠ 0 := by
    intro v hv h
    apply hv
    funext i
    exact σ.injective (by simpa using congrFun h i)
  have hact : ∀ (r : ↥(Rt M (LB M Q B) t)) (e : M₀.E), e ∈ M₀.img V →
      cV (φ ⟨(r : G), hc.Rt_le_H0 t r.2⟩ e) =
        ((ρ r).1 : Matrix (Fin 2) (Fin 2) K) * cV e * ((ρ r).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro r e he
    rw [hcV _ (phi_mem_img_Vt (hc := hc) ht φ hφπ r.2 he), hcV e he]
    exact hc0act r ⟨e, he⟩
  have hpoint : ∃ b : M₀.E, b ≠ 0 ∧ (∀ e, e ∈ M₀.img B ↔ ∃ c : K, e = c • b) ∧
      ∃ a a' : Fin 2 → K, a ≠ 0 ∧ a' ≠ 0 ∧ cV b = Matrix.vecMulVec a a' := by
    refine ⟨(e₀ : M₀.E), ?_, hBline, fun i => σ (a i), fun i => σ (a' i), hσinj a ha,
      hσinj a' ha', hcVe₀⟩
    intro h0
    apply C.hu0
    have h1 : e₀ = 0 := Subtype.ext h0
    rw [← hΨe₀, h1, map_zero]
  exact ⟨VDesc95Pre.mk cV ρ hinj hsurj hρsurj hact hpoint⟩

section Normalize

variable {K : Type} [Field K]

theorem coe_inv_mul_sl (a : SL(2, K)) :
    ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_mul_inv_sl (a : SL(2, K)) :
    (a : Matrix (Fin 2) (Fin 2) K) * ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem conj_tensor_identity (g₀ h₀ ρ₁ ρ₂ : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    (g₀ : Matrix (Fin 2) (Fin 2) K) * (((ρ₁ : Matrix (Fin 2) (Fin 2) K) * X *
        (ρ₂ : Matrix (Fin 2) (Fin 2) K)ᵀ) * (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ) =
      ((g₀ * ρ₁ * g₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        ((g₀ : Matrix (Fin 2) (Fin 2) K) * (X * (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ)) *
          ((h₀ * ρ₂ * h₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have e1 := coe_inv_mul_sl g₀
  have e2 : (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ * ((h₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ =
      1 := by
    rw [← Matrix.transpose_mul, coe_inv_mul_sl, Matrix.transpose_one]
  have e1' : ∀ Y : Matrix (Fin 2) (Fin 2) K, ((g₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      ((g₀ : Matrix (Fin 2) (Fin 2) K) * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  have e2' : ∀ Y : Matrix (Fin 2) (Fin 2) K, (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ *
      (((h₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, e2, Matrix.one_mul]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e1', e2']

end Normalize

section NormalizeDesc

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}

theorem exists_vdesc95_of_pre (P : VDesc95Pre hc t M₀ φ) : Nonempty (VDesc95 hc t M₀ φ) := by
  classical
  obtain ⟨b, hb0, hBline, a, a', ha, ha', hcb⟩ := P.point
  have h10 : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  obtain ⟨g₀, hg₀⟩ := exists_sl2_mulVec_eq ha h10
  obtain ⟨h₀, hh₀⟩ := exists_sl2_mulVec_eq ha' h10
  let Lm : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
    (LinearMap.mulLeft K (g₀ : Matrix (Fin 2) (Fin 2) K)).comp
      (LinearMap.mulRight K ((h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ))
  have hLm : ∀ X, Lm X = (g₀ : Matrix (Fin 2) (Fin 2) K) *
      (X * (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ) := fun X => rfl
  let Lm' : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
    (LinearMap.mulLeft K ((g₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)).comp
      (LinearMap.mulRight K (((h₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ))
  have hLm' : ∀ X, Lm' X = ((g₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      (X * ((h₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ) := fun X => rfl
  have e2 : (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ * ((h₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ =
      1 := by
    rw [← Matrix.transpose_mul, coe_inv_mul_sl, Matrix.transpose_one]
  have e3 : ((h₀⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ * (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ =
      1 := by
    rw [← Matrix.transpose_mul, coe_mul_inv_sl, Matrix.transpose_one]
  have hLL' : ∀ X, Lm' (Lm X) = X := by
    intro X
    rw [hLm', hLm]
    simp only [Matrix.mul_assoc]
    rw [e2, Matrix.mul_one, ← Matrix.mul_assoc, coe_inv_mul_sl, Matrix.one_mul]
  have hL'L : ∀ X, Lm (Lm' X) = X := by
    intro X
    rw [hLm, hLm']
    simp only [Matrix.mul_assoc]
    rw [e3, Matrix.mul_one, ← Matrix.mul_assoc, coe_mul_inv_sl, Matrix.one_mul]
  let δ : SL(2, K) × SL(2, K) := (g₀, h₀)
  have hρ' : ∀ z : SL(2, K) × SL(2, K), (MulAut.conj δ) z = (g₀ * z.1 * g₀⁻¹, h₀ * z.2 * h₀⁻¹) :=
    fun z => rfl
  refine ⟨⟨Lm ∘ₗ P.cV, (MulAut.conj δ).toMonoidHom.comp P.ρ, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro e he h0
    apply P.cV_inj e he
    have h1 : Lm (P.cV e) = 0 := h0
    have h2 := congrArg Lm' h1
    rwa [hLL', map_zero] at h2
  · intro X
    obtain ⟨e, he, hXe⟩ := P.cV_surj (Lm' X)
    exact ⟨e, he, by
      show Lm (P.cV e) = X
      rw [hXe, hL'L]⟩
  · intro z
    obtain ⟨r, hr⟩ := P.ρ_surj ((MulAut.conj δ).symm z)
    exact ⟨r, by
      show (MulAut.conj δ) (P.ρ r) = z
      rw [hr, MulEquiv.apply_symm_apply]⟩
  · intro r e he
    show Lm (P.cV (φ ⟨(r : G), hc.Rt_le_H0 t r.2⟩ e)) = _ * (Lm (P.cV e)) * _
    rw [P.cV_act r e he, hLm, hLm]
    have h1 : ((MulAut.conj δ).toMonoidHom.comp P.ρ) r =
        (g₀ * (P.ρ r).1 * g₀⁻¹, h₀ * (P.ρ r).2 * h₀⁻¹) := hρ' (P.ρ r)
    rw [h1]
    exact conj_tensor_identity g₀ h₀ (P.ρ r).1 (P.ρ r).2 (P.cV e)
  · refine ⟨b, hb0, hBline, ?_⟩
    show Lm (P.cV b) = _
    rw [hcb, hLm]
    have h1 : (g₀ : Matrix (Fin 2) (Fin 2) K) * (Matrix.vecMulVec a a' *
        (h₀ : Matrix (Fin 2) (Fin 2) K)ᵀ) =
        Matrix.vecMulVec ((g₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ a)
          ((h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ a') := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two] <;> ring
    rw [h1, hg₀, hh₀]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, Matrix.single_apply]

theorem exists_vdesc95 (h34 : Stroth34Statement) (hA : Sec9AExistsStatement) {n : ℕ}
    (hs : Sec9Hyp hc n t) [CharP K 2] (hglob : GlobalModelData M Q Z γ M₀)
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    Nonempty (VDesc95 hc t M₀ φ) := by
  obtain ⟨P⟩ := exists_vdescPre95 h34 hA hs hglob φ hφπ
  exact exists_vdesc95_of_pre P

end NormalizeDesc

end Coordinates

end HS9

end CFSG.RankThree.GF2n.Stroth80
