module

public import CFSG.RankThree.GF2n.Smith81.Orth28FourPlusModel
public import CFSG.RankThree.GF2n.Smith81.Orth28FourMinus
public import CFSG.RankThree.GF2n.Smith81.Orth28Sim
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormCube
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormFactors

public section

namespace CFSG.RankThree.GF2n.Smith81.FourPlus

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.RankThree.GF2n.Smith81.OrthTN CFSG.RankThree.GF2n.Smith81.D2
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Data (M Q Z B : Subgroup G) where
  hc : SmithOrthCfg M Q Z B
  C : OrthCtx M Q Z B
  card_ι : Fintype.card C.ι = 4
  tsp : ¬ NoTotallySingularPlane C.qU
  μ : (C.ι → C.K) ≃ₗ[C.K] Mat2 C.K
  det_eq : ∀ v, (μ v).det = C.qU v
  noA2 : NoA2 Q Z (LB M Q B)

namespace Data

variable (F : Data M Q Z B)

theorem hnd : (QuadraticMap.polarBilin F.C.qU).Nondegenerate :=
  polarBilin_nondegenerate_of_hnd F.C.hF.nondeg

theorem isPlus : CFSG.GroupTheory.WeirSylow.IsPlusType F.C.qU :=
  isPlusType_of_not_noTSP F.card_ι F.tsp

theorem four_le_card : 4 ≤ Nat.card F.C.K := by
  rw [F.C.hD.card]
  exact F.hc.ctx.hyp.q4

end Data

theorem exists_detModel (C : OrthCtx M Q Z B) (h4 : Fintype.card C.ι = 4)
    (hTSP : ¬ NoTotallySingularPlane C.qU) :
    ∃ μ : (C.ι → C.K) ≃ₗ[C.K] Mat2 C.K, ∀ v, (μ v).det = C.qU v := by
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have hdim : Module.finrank C.K (C.ι → C.K) = 2 * 2 := by
    rw [Module.finrank_fintype_fun_eq_card, h4]
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hnd hdim
    (isPlusType_of_not_noTSP h4 hTSP)
  refine ⟨e.toLinearEquiv.trans (detCoords C.K).symm, fun v => ?_⟩
  show ((detCoords C.K).symm (e v)).det = C.qU v
  rw [det_detCoords_symm]
  exact e.map_app v

@[expose] noncomputable def Data.ofFrame (hc : SmithOrthCfg M Q Z B) (hno : NoA2 Q Z (LB M Q B))
    (C : OrthCtx M Q Z B) (h4 : Fintype.card C.ι = 4) (hTSP : ¬ NoTotallySingularPlane C.qU) :
    Data M Q Z B where
  hc := hc
  C := C
  card_ι := h4
  tsp := hTSP
  μ := Classical.choose (exists_detModel C h4 hTSP)
  det_eq := Classical.choose_spec (exists_detModel C h4 hTSP)
  noA2 := hno

section Act

variable (F : Data M Q Z B)

noncomputable def actHom : ↥(H0 M Z) →* (F.C.M₀.E ≃ₗ[F.C.K] F.C.M₀.E) :=
  Classical.choose (exists_actionHom_H0 F.hc.ctx.hyp F.C.hD)

theorem actHom_π (m : ↥(H0 M Z)) (x : G) (hx : x ∈ Q) :
    F.C.M₀.π ((m : G) * x * (m : G)⁻¹) = actHom F m (F.C.M₀.π x) :=
  (Classical.choose_spec (exists_actionHom_H0 F.hc.ctx.hyp F.C.hD)).1 m x hx

@[expose] def coord : F.C.M₀.E ≃ₗ[F.C.K] Cube 3 F.C.K := F.C.φ.trans (thetaC F.μ)

@[expose] noncomputable def rhoC : ↥(H0 M Z) →* (Cube 3 F.C.K ≃ₗ[F.C.K] Cube 3 F.C.K) where
  toFun m := (coord F).symm.trans ((actHom F m).trans (coord F))
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    simp
  map_mul' m m' := by
    refine LinearEquiv.ext fun v => ?_
    simp

theorem rhoC_apply (m : ↥(H0 M Z)) (v : Cube 3 F.C.K) :
    rhoC F m v = coord F (actHom F m ((coord F).symm v)) := rfl

theorem rhoC_spec (m : ↥(H0 M Z)) (x : G) (hx : x ∈ Q) :
    rhoC F m (coord F (F.C.M₀.π x)) = coord F (F.C.M₀.π ((m : G) * x * (m : G)⁻¹)) := by
  rw [rhoC_apply, LinearEquiv.symm_apply_apply, actHom_π F m x hx]

theorem exists_coord_π (v : Cube 3 F.C.K) : ∃ x ∈ Q, coord F (F.C.M₀.π x) = v := by
  obtain ⟨x, hx, hxe⟩ := F.C.M₀.π_surj ((coord F).symm v)
  exact ⟨x, hx, by rw [hxe, LinearEquiv.apply_symm_apply]⟩

theorem actsAsTensor_swL_iff (m : ↥(H0 M Z)) (g h k : Mat2 F.C.K) :
    ActsAsTensor Q Z F.C.M₀ F.C.φ (m : G) g (swL F.μ h k) ↔
      ∀ v, rhoC F m v = kronMap ![g, h, k] v := by
  constructor
  · intro hact v
    obtain ⟨x, hx, rfl⟩ := exists_coord_π F v
    rw [rhoC_spec F m x hx]
    show thetaC F.μ (F.C.φ _) = kronMap ![g, h, k] (thetaC F.μ (F.C.φ _))
    rw [hact x hx, thetaC_orthTensor]
  · intro hk x hx
    have h1 := hk (coord F (F.C.M₀.π x))
    rw [rhoC_spec F m x hx] at h1
    have h2 : thetaC F.μ (F.C.φ (F.C.M₀.π ((m : G) * x * (m : G)⁻¹))) =
        thetaC F.μ (orthTensor g (swL F.μ h k) (F.C.φ (F.C.M₀.π x))) := by
      rw [thetaC_orthTensor]
      exact h1
    exact (thetaC F.μ).injective h2

end Act

section Lgen

variable (F : Data M Q Z B)

@[expose] def Lg : Subgroup ↥(H0 M Z) := (Lgen M (LB M Q B)).subgroupOf (H0 M Z)

theorem exists_kron_of_mem_Lgen (m : ↥(H0 M Z)) (hm : (m : G) ∈ Lgen M (LB M Q B)) :
    ∃ a b c : Mat2 F.C.K, a.det = 1 ∧ b.det = 1 ∧ c.det = 1 ∧
      ∀ v, rhoC F m v = kronMap ![a, b, c] v := by
  obtain ⟨g, o, hg, ho, hact⟩ := lgen_act_omega F.hc F.noA2 F.C hm
  obtain ⟨b, c, rfl⟩ := (mem_omegaGroup_iff_exists_swEquiv F.hnd F.det_eq F.four_le_card F.isPlus
    F.card_ι).mp ho
  refine ⟨g, b, c, hg, Matrix.SpecialLinearGroup.det_coe b, Matrix.SpecialLinearGroup.det_coe c,
    ?_⟩
  have h1 : ActsAsTensor Q Z F.C.M₀ F.C.φ (m : G) g
      (swL F.μ (b : Mat2 F.C.K) (c : Mat2 F.C.K)) := by
    rw [← coe_swEquiv]
    exact hact
  exact (actsAsTensor_swL_iff F m g b c).mp h1

theorem exists_lgen_rhoC (a b c : Mat2 F.C.K) (ha : a.det = 1) (hb : b.det = 1) (hc : c.det = 1) :
    ∃ m : ↥(H0 M Z), (m : G) ∈ Lgen M (LB M Q B) ∧ ∀ v, rhoC F m v = kronMap ![a, b, c] v := by
  have hS : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ Q, s * x * s⁻¹ ∈ Q := fun s hs x hx =>
    (F.hc.ctx.conj_mem_Q_of_mem_M (Lgen_le F.hc.ctx.LB_le_M hs)).1 x hx
  obtain ⟨s₁, hs₁, hact₁⟩ := F.C.hA.sl a ha
  set o : (F.C.ι → F.C.K) ≃ₗ[F.C.K] (F.C.ι → F.C.K) := swEquiv F.μ ⟨b, hb⟩ ⟨c, hc⟩ with ho
  have hoE : o ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup F.C.qU :=
    omegaGroup_le_elementaryGroup_of_cfg F.hc F.C
      (swEquiv_mem_omega F.hnd F.det_eq F.four_le_card _ _)
  obtain ⟨s₂, hs₂, hact₂⟩ := exists_lgen_actsAs_elementary F.C.hA hS hoE
  have hmul := ActsAsTensor.mul (o := LinearMap.id) (o' := (o : (F.C.ι → F.C.K) →ₗ[F.C.K] _))
    (hS s₂ hs₂) hact₁ hact₂
  have hmem : s₁ * s₂ ∈ Lgen M (LB M Q B) := Subgroup.mul_mem _ hs₁ hs₂
  refine ⟨⟨s₁ * s₂, Lgen_le_H0 F.hc.ctx hmem⟩, hmem, ?_⟩
  refine (actsAsTensor_swL_iff F ⟨s₁ * s₂, Lgen_le_H0 F.hc.ctx hmem⟩ a b c).mp ?_
  have e1 : (⇑(LinearMap.id ∘ₗ (o : (F.C.ι → F.C.K) →ₗ[F.C.K] _)) : (F.C.ι → F.C.K) → _) =
      swL F.μ b c := by
    funext v
    exact congrFun (coe_swEquiv F.μ ⟨b, hb⟩ ⟨c, hc⟩) v
  rw [e1, mul_one] at hmul
  exact hmul

theorem map_Lg_eq_cubeE :
    (Lg (M := M) (Q := Q) (Z := Z) (B := B)).map (rhoC F) = cubeE 3 F.C.K := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨a, b, c, ha, hb, hc, h⟩ := exists_kron_of_mem_Lgen F m hm
    refine mem_cubeE.mpr ⟨![a, b, c], fun i => ?_, h⟩
    fin_cases i <;> simpa
  · intro he
    obtain ⟨k, hk, hv⟩ := mem_cubeE.mp he
    obtain ⟨m, hm, hmv⟩ := exists_lgen_rhoC F (k 0) (k 1) (k 2) (hk 0) (hk 1) (hk 2)
    have hk3 : ![k 0, k 1, k 2] = k := by
      funext i
      fin_cases i <;> rfl
    exact ⟨m, hm, LinearEquiv.ext fun v => by rw [hmv, hk3, hv]⟩

theorem rhoC_conj_mem_cubeE (m : ↥(H0 M Z)) {e : Cube 3 F.C.K ≃ₗ[F.C.K] Cube 3 F.C.K}
    (he : e ∈ cubeE 3 F.C.K) : rhoC F m * e * (rhoC F m)⁻¹ ∈ cubeE 3 F.C.K := by
  rw [← map_Lg_eq_cubeE F] at he ⊢
  obtain ⟨l, hl, rfl⟩ := he
  refine ⟨m * l * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) m.2.1) (l : G)).mp hl
  show ((m * l * m⁻¹ : ↥(H0 M Z)) : G) ∈ Lgen M (LB M Q B)
  simpa using h1

end Lgen

section Perm

variable (F : Data M Q Z B)

theorem exists_perm_cube (m : ↥(H0 M Z)) :
    ∃ π : Equiv.Perm (Fin 3), ∀ (i : Fin 3) (x : Cube 3 F.C.K ≃ₗ[F.C.K] Cube 3 F.C.K),
      x ∈ cubeF 3 F.C.K i ↔ rhoC F m * x * (rhoC F m)⁻¹ ∈ cubeF 3 F.C.K (π i) :=
  (threeFactors F.four_le_card).exists_perm (rhoC F m)
    (fun _ hx => rhoC_conj_mem_cubeE F m hx)
    (fun _ hx => by simpa [map_inv] using rhoC_conj_mem_cubeE F m⁻¹ hx)

@[expose] noncomputable def permOf (m : ↥(H0 M Z)) : Equiv.Perm (Fin 3) :=
  Classical.choose (exists_perm_cube F m)

theorem permOf_spec (m : ↥(H0 M Z)) (i : Fin 3)
    (x : Cube 3 F.C.K ≃ₗ[F.C.K] Cube 3 F.C.K) :
    x ∈ cubeF 3 F.C.K i ↔ rhoC F m * x * (rhoC F m)⁻¹ ∈ cubeF 3 F.C.K (permOf F m i) :=
  Classical.choose_spec (exists_perm_cube F m) i x

theorem permOf_unique (m : ↥(H0 M Z)) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ (i : Fin 3) (x : Cube 3 F.C.K ≃ₗ[F.C.K] Cube 3 F.C.K),
      x ∈ cubeF 3 F.C.K i ↔ rhoC F m * x * (rhoC F m)⁻¹ ∈ cubeF 3 F.C.K (π i)) :
    π = permOf F m := by
  refine Equiv.ext fun i => ?_
  by_contra hne
  have hcF : cubeF 3 F.C.K (π i) = cubeF 3 F.C.K (permOf F m i) := by
    set T := rhoC F m with hT
    ext y
    have e : T * (T⁻¹ * y * T) * T⁻¹ = y := by group
    constructor
    · intro hy
      have hx : T⁻¹ * y * T ∈ cubeF 3 F.C.K i := (hπ i _).mpr (by rw [e]; exact hy)
      have := (permOf_spec F m i _).mp hx
      rwa [e] at this
    · intro hy
      have hx : T⁻¹ * y * T ∈ cubeF 3 F.C.K i := (permOf_spec F m i _).mpr (by rw [e]; exact hy)
      have := (hπ i _).mp hx
      rwa [e] at this
  exact (threeFactors F.four_le_card).ne hne hcF

@[expose] noncomputable def permHom : ↥(H0 M Z) →* Equiv.Perm (Fin 3) :=
  MonoidHom.mk' (permOf F) fun m m' => by
    symm
    refine permOf_unique F (m * m') (permOf F m * permOf F m') fun i x => ?_
    have h1 := permOf_spec F m' i x
    have h2 := permOf_spec F m (permOf F m' i) (rhoC F m' * x * (rhoC F m')⁻¹)
    have e : rhoC F (m * m') * x * (rhoC F (m * m'))⁻¹ =
        rhoC F m * (rhoC F m' * x * (rhoC F m')⁻¹) * (rhoC F m)⁻¹ := by
      rw [map_mul]
      group
    rw [e, Equiv.Perm.mul_apply]
    exact h1.trans h2

theorem exists_actMap_conj (m : ↥(H0 M Z)) (i : Fin 3) (A : Mat2 F.C.K) (hA : A.det = 1) :
    ∃ A' : Mat2 F.C.K, A'.det = 1 ∧
      ∀ v, rhoC F m (actMap i A v) = actMap (permHom F m i) A' (rhoC F m v) := by
  have hmem := (permOf_spec F m i (actSL i ⟨A, hA⟩)).mp (actSL_mem i ⟨A, hA⟩)
  obtain ⟨A', hA', hA'v⟩ := mem_cubeF.mp hmem
  refine ⟨A', hA', fun v => ?_⟩
  have := hA'v (rhoC F m v)
  have e : actSL i ⟨A, hA⟩ v = actMap i A v := actSL_apply i ⟨A, hA⟩ v
  rw [← e]
  have h2 : rhoC F m (actSL i ⟨A, hA⟩ v) = actMap (permOf F m i) A' (rhoC F m v) := by
    simpa using this
  exact h2

theorem exists_kron_of_permHom_eq_one (m : ↥(H0 M Z)) (hm : permHom F m = 1) :
    ∃ h : Fin 3 → Mat2 F.C.K, (∀ i, IsUnit (h i).det) ∧ ∀ v, rhoC F m v = kronMap h v := by
  have hT : ∀ i : Fin 3, ∀ A : Mat2 F.C.K, A.det = 1 → ∃ A' : Mat2 F.C.K, A'.det = 1 ∧
      ∀ v, rhoC F m (actMap i A v) = actMap ((1 : Equiv.Perm (Fin 3)) i) A' (rhoC F m v) := by
    intro i A hA
    obtain ⟨A', hA', h⟩ := exists_actMap_conj F m i A hA
    exact ⟨A', hA', by rw [hm] at h; exact h⟩
  obtain ⟨h, hu, hh⟩ := exists_kron_perm (rhoC F m) (1 : Equiv.Perm (Fin 3)) hT
  exact ⟨h, hu, fun v => by rw [hh v, permMap_one]; rfl⟩

theorem mem_Lgen_of_permHom_eq_one (m : ↥(H0 M Z)) (hm : permHom F m = 1) (hm2 : m * m = 1) :
    (m : G) ∈ Lgen M (LB M Q B) := by
  obtain ⟨h, hu, hh⟩ := exists_kron_of_permHom_eq_one F m hm
  have hsq : kronMap h ∘ₗ kronMap h = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    have := LinearEquiv.congr_fun (map_mul (rhoC F) m m) v
    rw [hm2, map_one] at this
    simp only [LinearEquiv.mul_apply, hh, LinearEquiv.coe_one, id] at this
    simpa using this.symm
  obtain ⟨s, hs, hks⟩ := exists_sl_of_involution h hu hsq
  have hs3 : ![s 0, s 1, s 2] = s := by
    funext i
    fin_cases i <;> rfl
  set o : (F.C.ι → F.C.K) ≃ₗ[F.C.K] (F.C.ι → F.C.K) :=
    swEquiv F.μ ⟨s 1, hs 1⟩ ⟨s 2, hs 2⟩ with ho
  have hoE : o ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup F.C.qU :=
    omegaGroup_le_elementaryGroup_of_cfg F.hc F.C
      (swEquiv_mem_omega F.hnd F.det_eq F.four_le_card _ _)
  have hact : ActsAsTensor Q Z F.C.M₀ F.C.φ (m : G) (s 0) (swL F.μ (s 1) (s 2)) := by
    refine (actsAsTensor_swL_iff F m _ _ _).mpr fun v => ?_
    rw [hh v, hks, hs3]
  have hact' : ActsAsTensor Q Z F.C.M₀ F.C.φ (m : G) (s 0) ⇑o := by
    have : ⇑o = swL F.μ (s 1) (s 2) := coe_swEquiv F.μ ⟨s 1, hs 1⟩ ⟨s 2, hs 2⟩
    rw [this]
    exact hact
  exact mem_Lgen_of_act_elementary F.hc F.C m.2.1 (hs 0) hoE hact'

end Perm

end CFSG.RankThree.GF2n.Smith81.FourPlus
