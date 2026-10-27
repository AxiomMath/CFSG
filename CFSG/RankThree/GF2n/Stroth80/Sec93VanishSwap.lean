module

public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishNotSing
public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishReflection
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93One
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreX
public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishIsom
public import CFSG.RankThree.GF2n.Stroth80.Sec7NormalizerOmega

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS93


theorem exists_fx_sec9 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {X : Subgroup (GL ι K)}
    (hX : AddCommutantScalar X) (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {y : G} (hyM : y ∈ M) (hyH : y ∈ H0 M Z)
    (hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t) :
    ∃ F : (ι → K) →ₗ[K] (ι → K), ∀ (k k' : ↥(Vt M (LB M Q B) B Z t)),
      (k' : G) = y * k * y⁻¹ → F (secVec ψ k) = secVec ψ k' := by
  classical
  obtain ⟨Kg, fKg, finKg, chKg, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hcard : Nat.card Kg = Nat.card K := by rw [h.card, hK]
  have hSmul : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun c e he => hc.smul_mem_img_Vt h t c he
  have hlin : ∀ r ∈ Rt M (LB M Q B) t, ∃ T : M₀.E →ₗ[Kg] M₀.E,
      ∀ q ∈ Q, M₀.π (r * q * r⁻¹) = T (M₀.π q) := fun r hr =>
    ⟨(φ₀ ⟨r, hc.Rt_le_H0 t hr⟩).toLinearMap, fun q hq => hφπ ⟨r, hc.Rt_le_H0 t hr⟩ q hq⟩
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcard M₀ hVQ hX hSmul hlin φ hφ
    (hc.Rt_normalizes_Vt ht) ψ hψ
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  let ν : ↥(Vt M (LB M Q B) B Z t) →* ↥(Vt M (LB M Q B) B Z t) :=
    { toFun := fun k => ⟨y * k * y⁻¹, hyV k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hν : Z.subgroupOf (Vt M (LB M Q B) B Z t) ≤
      (Z.subgroupOf (Vt M (LB M Q B) B Z t)).comap ν := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hZn y hyM z hz
  let f : Multiplicative (ι → K) →* Multiplicative (ι → K) :=
    ψ.toMonoidHom.comp ((QuotientGroup.map _ _ ν hν).comp ψ.symm.toMonoidHom)
  let Fa : (ι → K) →+ (ι → K) :=
    { toFun := fun w => Multiplicative.toAdd (f (Multiplicative.ofAdd w))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add, toAdd_mul] }
  have hFa : ∀ k : ↥(Vt M (LB M Q B) B Z t),
      Fa (secVec ψ k) = secVec ψ ⟨y * k * y⁻¹, hyV k k.2⟩ := by
    intro k
    show Multiplicative.toAdd (f (Multiplicative.ofAdd (secVec ψ k))) = _
    unfold secVec
    rw [ofAdd_toAdd]
    show Multiplicative.toAdd (ψ ((QuotientGroup.map _ _ ν hν) (ψ.symm (ψ (QuotientGroup.mk k)))))
      = _
    rw [MulEquiv.symm_apply_apply, QuotientGroup.map_mk]
    rfl
  have hsurj : ∀ w : ι → K, ∃ k : ↥(Vt M (LB M Q B) B Z t), secVec ψ k = w :=
    fun w => exists_secVec_eq ψ w
  refine ⟨{ toFun := Fa, map_add' := Fa.map_add, map_smul' := ?_ }, ?_⟩
  · intro c w
    obtain ⟨k, rfl⟩ := hsurj w
    obtain ⟨k₁, hk₁V, hk₁Q, hk₁π⟩ := hSmul (θ.symm c) (M₀.π k)
      (M₀.pi_mem_img k.2 (hVQ k.2))
    have hk₁ : secVec ψ ⟨k₁, hk₁V⟩ = c • secVec ψ k := by
      have := hθ (θ.symm c) k ⟨k₁, hk₁V⟩ hk₁π
      rw [RingEquiv.apply_symm_apply] at this
      exact this
    have e1 : Fa (c • secVec ψ k) = secVec ψ ⟨y * k₁ * y⁻¹, hyV k₁ hk₁V⟩ := by
      rw [← hk₁]
      exact hFa ⟨k₁, hk₁V⟩
    have hπ2 : M₀.π (y * k₁ * y⁻¹) = θ.symm c • M₀.π (y * (k : G) * y⁻¹) := by
      have h1 := hφπ ⟨y, hyH⟩ k₁ hk₁Q
      have h2 := hφπ ⟨y, hyH⟩ (k : G) (hVQ k.2)
      simp only at h1 h2
      rw [h1, h2, hk₁π, map_smul]
    have e2 := hθ (θ.symm c) ⟨y * k * y⁻¹, hyV k k.2⟩ ⟨y * k₁ * y⁻¹, hyV k₁ hk₁V⟩ hπ2
    rw [RingEquiv.apply_symm_apply] at e2
    show Fa (c • secVec ψ k) = c • Fa (secVec ψ k)
    rw [e1, hFa k]
    exact e2
  · intro k k' hk'
    have : k' = ⟨y * k * y⁻¹, hyV k k.2⟩ := Subtype.ext hk'
    subst this
    exact hFa k


theorem Fx_conj {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (ht : t ∈ LB M Q B) {x : G} (hxM : x ∈ M)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t)
    (hx2 : x ^ 2 ∈ Q) (Fx : (ι → K) →ₗ[K] (ι → K))
    (hFx : ∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = x * k * x⁻¹ →
      Fx (secVec ψ k) = secVec ψ k')
    (a : ↥(Rt M (LB M Q B) t)) (ha' : x * (a : G) * x⁻¹ ∈ Rt M (LB M Q B) t) (w : ι → K) :
    Fx ((φ a : Matrix ι ι K) *ᵥ Fx w) = (φ ⟨x * (a : G) * x⁻¹, ha'⟩ : Matrix ι ι K) *ᵥ w := by
  classical
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hRM : ∀ y ∈ Rt M (LB M Q B) t, y ∈ M := fun y hy => hc.Rt_le_M t hy
  obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
  have ha'M : x * (a : G) * x⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hxM (hRM a a.2)) (M.inv_mem hxM)
  have eL : Fx ((φ a : Matrix ι ι K) *ᵥ Fx (secVec ψ k)) =
      secVec ψ ⟨x * ((a : G) * (x * k * x⁻¹) * (a : G)⁻¹) * x⁻¹,
        hxV _ (hVR a a.2 _ (hxV k k.2))⟩ := by
    have e1 : Fx (secVec ψ k) = secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ :=
      hFx k ⟨x * k * x⁻¹, hxV k k.2⟩ rfl
    rw [e1]
    have e2 : (φ a : Matrix ι ι K) *ᵥ secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ =
        secVec ψ ⟨(a : G) * (x * k * x⁻¹) * (a : G)⁻¹, hVR a a.2 _ (hxV k k.2)⟩ :=
      (hψ a ⟨x * k * x⁻¹, hxV k k.2⟩ _ rfl).symm
    rw [e2]
    exact hFx _ _ rfl
  have eR : (φ ⟨x * (a : G) * x⁻¹, ha'⟩ : Matrix ι ι K) *ᵥ secVec ψ k =
      secVec ψ ⟨x * (a : G) * x⁻¹ * k * (x * (a : G) * x⁻¹)⁻¹, hVR _ ha' k k.2⟩ :=
    (hψ ⟨x * (a : G) * x⁻¹, ha'⟩ k _ rfl).symm
  rw [eL, eR, secVec_eq_iff]
  have hcomm : ⁅x ^ 2, (k : G)⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx2 (hVQ k.2)
  have hz : x * (a : G) * x⁻¹ * ⁅x ^ 2, (k : G)⁆ * (x * (a : G) * x⁻¹)⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha'M) _).mp hcomm
  convert hz using 1
  simp only [commutatorElement_def, pow_two, Subgroup.coe_mk]
  group


theorem Vt_eq_comm_of_centre (hCentre : Step95CentreStatement) {hc : Ctx M Q Z B} {n : ℕ}
    {t : G} (hs : Sec9Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s z : G} (hT : Sec9T1 M Q Z0 s z) :
    Vt M (LB M Q B) B Z t = ⁅Q, Subgroup.zpowers s⁆ ⊔ Z := by
  obtain ⟨-, -, hV⟩ := hCentre G M Q Z B hc n t hs Z0 hZ0
  have ht : t ∈ LB M Q B := hs.mem
  have hQZ0 : Q ≤ Z0 := fun a ha => (hZ0 a).mpr ⟨hc.Q_le_Rt ht ha, fun r hr => by
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have h1 := norm_Q hc hrM (Q.inv_mem ha)
    have e : ⁅a, r⁆ = a * (r * a⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem ha h1⟩
  have hsQ : s ∉ Q := fun hsQ => hT.not_mem (hQZ0 (norm_Q hc hT.z_mem hsQ))
  exact (hV s hT.s_mem hsQ).symm



theorem false_of_normalizes_R0 (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G} (hxM : x ∈ M)
    (hxH : x ∈ H0 M Z) (hx2 : x ^ 2 ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t)
    (hxR : ∀ y ∈ Rt M (LB M Q B) t, x * y * x⁻¹ ∈ Rt M (LB M Q B) t)
    (hsing : ∀ k ∈ Vt M (LB M Q B) B Z t, HS9.IsSingV M Q Z B t ⁅x, k⁆ → ⁅x, k⁆ ∈ Z)
    (hne : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z)
    (R₀ : Subgroup G) (hNR₀ : hc.CN t ≤ R₀) (hR₀R : R₀ ≤ Rt M (LB M Q B) t)
    (hR₀norm : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ R₀ = R₀) (hR₀N : R₀ ≠ hc.CN t)
    (hR₀R' : R₀ ≠ Rt M (LB M Q B) t) (hxR₀ : ∀ a ∈ R₀, x * a * x⁻¹ ∈ R₀) : False := by
  classical
  obtain ⟨K, fK, finK, chK, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  have ht : t ∈ LB M Q B := hs.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hK4 : 4 ≤ Nat.card K := P.card ▸ hq4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hK4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have hX := addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩
  obtain ⟨Fx, hFx⟩ := exists_fx_sec9 hc ht P.card hX φ P.range ψ P.act hxM hxH hxV
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hFFx : ∀ w, Fx (Fx w) = w := by
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    set k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k * x⁻¹, hxV k k.2⟩ with hk₁
    set k₂ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k₁ * x⁻¹, hxV k₁ k₁.2⟩ with hk₂
    have e1 : Fx (secVec ψ k) = secVec ψ k₁ := hFx k k₁ rfl
    have e2 : Fx (secVec ψ k₁) = secVec ψ k₂ := hFx k₁ k₂ rfl
    rw [e1, e2, secVec_eq_iff]
    have e3 : (k₂ : G) * (k : G)⁻¹ = ⁅x ^ 2, (k : G)⁆ := by
      rw [hk₂, hk₁]
      simp only [commutatorElement_def, pow_two]
      group
    rw [e3]
    exact Smith81.comm_mem_Z hc.hyp hx2 (hVQ k.2)
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  have hN : ∀ A : GL (Fin 2 ⊕ Fin 2) K,
      (∀ g ∈ StatedOmega (StatedQuadPlus 2 K), A * g * A⁻¹ ∈ StatedOmega (StatedQuadPlus 2 K)) →
      ∃ c : K, c ≠ 0 ∧ ∀ v, quadPlus 2 K
        (c • ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)) = quadPlus 2 K v := by
    intro A hA
    obtain ⟨c, hc0', hcv⟩ := normalizerOmegaFor_plus K hK4 (le_refl 2) A hA
    exact ⟨c, hc0', fun v => by rw [coe_quadPlus]; exact hcv v⟩
  have hcompat : ∀ g ∈ StatedOmega (StatedQuadPlus 2 K), ∃ g' ∈ StatedOmega (StatedQuadPlus 2 K),
      ∀ w, Fx ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Fx w) =
        (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w := by
    intro g hg
    have hgR : g ∈ φ.range := by rw [P.range]; exact hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hgR
    have ha' : x * (a : G) * x⁻¹ ∈ Rt M (LB M Q B) t := hxR a a.2
    refine ⟨φ ⟨x * (a : G) * x⁻¹, ha'⟩, ?_, fun w =>
      Fx_conj (hc := hc) φ ψ P.act ht hxM hxV hx2 Fx hFx a ha' w⟩
    rw [← P.range]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have iso : ∀ v, quadPlus 2 K (Fx v) = quadPlus 2 K v :=
    vanishGeom_isometry_of_normalizer hQnd hN Fx hFFx hcompat
  let MF : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := LinearMap.toMatrix' Fx
  have hmul : ∀ w, MF *ᵥ w = Fx w := fun w => LinearMap.toMatrix'_mulVec Fx w
  have hMF : MF * MF = 1 := by
    have h1 : LinearMap.toMatrix' (Fx ∘ₗ Fx) = LinearMap.toMatrix' LinearMap.id := by
      rw [show Fx ∘ₗ Fx = LinearMap.id from LinearMap.ext hFFx]
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h1
    exact h1
  let Xg : GL (Fin 2 ⊕ Fin 2) K := ⟨MF, MF, hMF, hMF⟩
  have hXg : ((Xg : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = MF := rfl
  have hXinv : Xg⁻¹ = Xg := inv_eq_of_mul_eq_one_right (Units.ext hMF)
  have hneg : ∀ v : Fin 2 ⊕ Fin 2 → K, -v = v := fun v => by
    ext i
    simp [CharTwo.neg_eq]
  have hXiso : ∀ v, StatedQuadPlus 2 K
      (((Xg : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        StatedQuadPlus 2 K v := by
    intro v
    rw [hXg, hmul, ← coe_quadPlus]
    exact iso v
  have hXinvol : ∀ v, ((Xg : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((Xg : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = v := by
    intro v
    rw [hXg, hmul, hmul]
    exact hFFx v
  have hXne : ∃ v, ((Xg : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ≠ v := by
    obtain ⟨v₀, hv₀, hv₀Z⟩ := hne
    refine ⟨secVec ψ ⟨v₀, hv₀⟩, fun h => hv₀Z ?_⟩
    rw [hXg, hmul] at h
    have hk : Fx (secVec ψ ⟨v₀, hv₀⟩) = secVec ψ ⟨x * v₀ * x⁻¹, hxV v₀ hv₀⟩ :=
      hFx ⟨v₀, hv₀⟩ ⟨x * v₀ * x⁻¹, hxV v₀ hv₀⟩ rfl
    rw [hk] at h
    have := (secVec_eq_iff ψ ⟨x * v₀ * x⁻¹, hxV v₀ hv₀⟩ ⟨v₀, hv₀⟩).mp h
    simpa [commutatorElement_def, mul_assoc] using this
  have hns : ∀ v, StatedQuadPlus 2 K
      (((Xg : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + v) = 0 →
        ((Xg : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ v
    let k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k * x⁻¹, hxV k k.2⟩
    let cV : ↥(Vt M (LB M Q B) B Z t) :=
      ⟨⁅x, (k : G)⁆, (Vt M (LB M Q B) B Z t).mul_mem (hxV k k.2)
        ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩
    have hFk : Fx (secVec ψ k) = secVec ψ k₁ := hFx k k₁ rfl
    have hcv : secVec ψ cV = MF *ᵥ secVec ψ k + secVec ψ k := by
      rw [hmul, hFk]
      have e : cV = k₁ * k⁻¹ := Subtype.ext (by simp [cV, k₁, commutatorElement_def, mul_assoc])
      rw [e, secVec_mul, secVec_inv, hneg]
    rw [hXg] at hv0 hv
    have hQw : quadPlus 2 K (secVec ψ cV) = 0 := by
      rw [hcv, coe_quadPlus]
      exact hv
    have hz0 : secVec ψ cV ≠ 0 := by rw [hcv]; exact hv0
    obtain ⟨A, hA, hAu⟩ := E.exists_mulVec_eq hQnd (P := plusPair K 0) (P' := plusPair K 1)
      (plusPair_orth (by decide)) P.ne_zero hz0 (by rw [P.sing, hQw])
    obtain ⟨ρ, hρ⟩ := MonoidHom.mem_range.mp (P.range ▸ hA)
    obtain ⟨b, hbB, hbs⟩ := (P.point u).mpr ⟨1, (one_smul K u).symm⟩
    have hsingc : HS9.IsSingV M Q Z B t ⁅x, (k : G)⁆ := by
      refine ⟨ρ, ρ.2, b, hbB, ?_⟩
      have hbV : (b : G) ∈ Vt M (LB M Q B) B Z t := b.2
      have hb' : secVec ψ ⟨(ρ : G) * b * (ρ : G)⁻¹, hVR ρ ρ.2 b hbV⟩ =
          (φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ b :=
        P.act ρ b ⟨(ρ : G) * b * (ρ : G)⁻¹, hVR ρ ρ.2 b hbV⟩ rfl
      rw [hρ, hbs, hAu] at hb'
      exact (secVec_eq_iff ψ cV _).mp hb'.symm
    exact hz0 ((secVec_eq_zero_iff ψ cV).mpr (hsing k k.2 hsingc))
  set A : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
    (R₀.subgroupOf (Rt M (LB M Q B) t)).map φ with hA
  have hAΩ : A ≤ StatedOmega (StatedQuadPlus 2 K) := by
    rw [← P.range]
    exact Subgroup.map_le_range φ _
  have hAnorm : ∀ g ∈ StatedOmega (StatedQuadPlus 2 K), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    rw [← P.range] at hg
    obtain ⟨ρ, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨ρ * r * ρ⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    have h := conj_mem' (ρ : G) hr
    rw [hR₀norm ρ ρ.2] at h
    simpa using h
  have hkerN : ∀ r : ↥(Rt M (LB M Q B) t), φ r = 1 → (r : G) ∈ hc.CN t := by
    intro r hr
    have : r ∈ φ.ker := hr
    rw [P.ker] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hA0 : A ≠ ⊥ := by
    obtain ⟨r, hr, hrN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hNR₀ (Ne.symm hR₀N))
    intro h
    have hmem : φ ⟨r, hR₀R hr⟩ ∈ A :=
      Subgroup.mem_map.mpr ⟨⟨r, hR₀R hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hrN (hkerN _ hmem)
  have hAΩ' : A ≠ StatedOmega (StatedQuadPlus 2 K) := by
    obtain ⟨ρ, hρR, hρ₀⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hR₀R hR₀R')
    intro h
    have hmem : φ ⟨ρ, hρR⟩ ∈ A := by
      rw [h, ← P.range]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨r, hr, hrρ⟩ := Subgroup.mem_map.mp hmem
    have hr0 : (r : G) ∈ R₀ := Subgroup.mem_subgroupOf.mp hr
    have h1 : φ (r⁻¹ * ⟨ρ, hρR⟩) = 1 := by rw [map_mul, map_inv, hrρ, inv_mul_cancel]
    have h2 := hkerN _ h1
    apply hρ₀
    have e : ρ = (r : G) * ((r : G)⁻¹ * ρ) := by group
    rw [e]
    exact R₀.mul_mem hr0 (hNR₀ h2)
  obtain ⟨a, haA, haX⟩ := exists_conj_notMem_of_reflection hK4 Xg hXiso hXinvol hXne hns A hAΩ
    hAnorm hA0 hAΩ'
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp haA
  have hr0 : (r : G) ∈ R₀ := Subgroup.mem_subgroupOf.mp hr
  have hxr : x * (r : G) * x⁻¹ ∈ Rt M (LB M Q B) t := hxR r r.2
  have heq : Xg * φ r * Xg⁻¹ = φ ⟨x * (r : G) * x⁻¹, hxr⟩ := by
    apply Units.ext
    apply vanishGeom_matrix_eq_of_mulVec
    intro w
    rw [hXinv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    show MF *ᵥ ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (MF *ᵥ w)) = _
    rw [hmul, hmul]
    exact Fx_conj (hc := hc) φ ψ P.act ht hxM hxV hx2 Fx hFx r hxr w
  apply haX
  rw [heq]
  exact Subgroup.mem_map.mpr ⟨⟨x * (r : G) * x⁻¹, hxr⟩,
    Subgroup.mem_subgroupOf.mpr (hxR₀ _ hr0), rfl⟩

theorem comm_mem_conj_Vt (hCentre : Step95CentreStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {s z : G} (hT : Sec9T1 M Q Z0 s z) {k : G} (hk : k ∈ Vt M (LB M Q B) B Z t) :
    ⁅z * s * z⁻¹, k⁆ ∈ conjSubgroup z (Vt M (LB M Q B) B Z t) := by
  rw [mem_conjSubgroup]
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hq : z⁻¹ * k * z ∈ Q := by
    have := norm_Q hc (M.inv_mem hT.z_mem) (hVQ hk)
    simpa using this
  have hcomm : ⁅z⁻¹ * k * z, s⁆ ∈ (⁅Q, Subgroup.zpowers s⁆ : Subgroup G) :=
    Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers s)
  have e : z⁻¹ * ⁅z * s * z⁻¹, k⁆ * z = ⁅z⁻¹ * k * z, s⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, Vt_eq_comm_of_centre hCentre hs hZ0 hT]
  exact Subgroup.mem_sup_left ((⁅Q, Subgroup.zpowers s⁆ : Subgroup G).inv_mem hcomm)

end HS93


theorem step93VanishSwap_of_claims (h34 : Stroth34Statement) (h1 : Step93OneStatement)
    (hCentre : Step95CentreStatement) : Step93VanishSwapStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT hne R₀ hNR₀ hR₀R hR₀norm hR₀N hR₀R'
    hxR₀eq
  have ht : t ∈ LB M Q B := hs.mem
  have hsR : s ∈ Rt M (LB M Q B) t := ((hZ0 s).mp hT.s_mem).1
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hxM : z * s * z⁻¹ ∈ M := M.mul_mem (M.mul_mem hT.z_mem hsM) (M.inv_mem hT.z_mem)
  have hxV' := HS93.conj_Vt_of_centre hCentre hs hZ0 hT
  have hxR' := HS93.conj_Rt_of_one h1 hs hr hZ0 hsc hxM hxV'
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, z * s * z⁻¹ * v * (z * s * z⁻¹)⁻¹ ∈
      Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxV') v).mp hv
  have hxR : ∀ y ∈ Rt M (LB M Q B) t, z * s * z⁻¹ * y * (z * s * z⁻¹)⁻¹ ∈
      Rt M (LB M Q B) t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxR') y).mp hy
  have hxH : z * s * z⁻¹ ∈ H0 M Z := hc.conj_mem_H0 hT.z_mem (hc.Rt_le_H0 t hsR)
  have hsL : s ∈ LB M Q B := (((hCentre G M Q Z B hc n t hs Z0 hZ0).1) hT.s_mem).1
  have hx2 : (z * s * z⁻¹) ^ 2 ∈ Q := by
    have e : (z * s * z⁻¹) ^ 2 = z * s ^ 2 * z⁻¹ := by
      simp only [pow_two]
      group
    rw [e]
    exact HS93.norm_Q hc hT.z_mem (hc.sq_mem_Q_of_mem_LB hsL)
  have hsing : ∀ k ∈ Vt M (LB M Q B) B Z t, HS9.IsSingV M Q Z B t ⁅z * s * z⁻¹, k⁆ →
      ⁅z * s * z⁻¹, k⁆ ∈ Z := by
    intro k hk hsk
    have hkV : ⁅z * s * z⁻¹, k⁆ ∈ Vt M (LB M Q B) B Z t :=
      (Vt M (LB M Q B) B Z t).mul_mem (hxV k hk) ((Vt M (LB M Q B) B Z t).inv_mem hk)
    exact HS93.notSing_inf_conj h1 hCentre hs hr hZ0 hsc hT _
      ⟨hkV, HS93.comm_mem_conj_Vt hCentre hs hZ0 hT hk⟩ hsk
  exact HS93.false_of_normalizes_R0 h34 hs hxM hxH hx2 hxV hxR hsing hne R₀ hNR₀ hR₀R hR₀norm hR₀N
    hR₀R' (fun a ha => by
      have h := HS93.conj_mem' (z * s * z⁻¹) ha
      rwa [hxR₀eq] at h)

theorem step93VanishSwap_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) : Step93VanishSwapStatement :=
  step93VanishSwap_of_claims h34 (step93One_of h34 h311a h311bComm h312b)
    (step95Centre_of h34 h311a h311bComm h311bCard)

end CFSG.RankThree.GF2n.Stroth80
