module

public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishCountGrp
public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishRefl
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9N5

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS93


theorem secVec_conj_conj {hc : Ctx M Q Z B} {t : G} (ht : t ∈ LB M Q B) {K : Type} [Field K]
    {ι : Type} [Fintype ι] [DecidableEq ι] [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {x : G} (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t)
    (Fx : (ι → K) →ₗ[K] (ι → K))
    (hFx : ∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = x * k * x⁻¹ →
      Fx (secVec ψ k) = secVec ψ k')
    (g : ↥(Rt M (LB M Q B) t)) (b : ↥(Vt M (LB M Q B) B Z t))
    (hb : (g : G) * x * (g : G)⁻¹ * (b : G) * ((g : G) * x * (g : G)⁻¹)⁻¹ ∈
      Vt M (LB M Q B) B Z t) :
    secVec ψ ⟨(g : G) * x * (g : G)⁻¹ * (b : G) * ((g : G) * x * (g : G)⁻¹)⁻¹, hb⟩ =
      (φ g : Matrix ι ι K) *ᵥ Fx ((((φ g)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ secVec ψ b) := by
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hb1 : (g : G)⁻¹ * (b : G) * (g : G) ∈ Vt M (LB M Q B) B Z t := by
    have := hVR ((g⁻¹ : ↥(Rt M (LB M Q B) t)) : G) (g⁻¹).2 b b.2
    simpa using this
  set b₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨(g : G)⁻¹ * (b : G) * (g : G), hb1⟩ with hb₁
  have h1 : secVec ψ b₁ = (((φ g)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ secVec ψ b := by
    have := hψ g⁻¹ b b₁ (by simp [hb₁])
    rw [map_inv] at this
    exact this
  set b₂ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * (b₁ : G) * x⁻¹, hxV _ b₁.2⟩ with hb₂
  have h2 : secVec ψ b₂ = Fx (secVec ψ b₁) := (hFx b₁ b₂ rfl).symm
  have hb3 : (g : G) * (b₂ : G) * (g : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := hVR g g.2 b₂ b₂.2
  set b₃ : ↥(Vt M (LB M Q B) B Z t) := ⟨(g : G) * (b₂ : G) * (g : G)⁻¹, hb3⟩ with hb₃
  have h3 : secVec ψ b₃ = (φ g : Matrix ι ι K) *ᵥ secVec ψ b₂ := hψ g b₂ b₃ rfl
  have heq : (⟨(g : G) * x * (g : G)⁻¹ * (b : G) * ((g : G) * x * (g : G)⁻¹)⁻¹, hb⟩ :
      ↥(Vt M (LB M Q B) B Z t)) = b₃ := by
    apply Subtype.ext
    simp only [hb₃, hb₂, hb₁]
    group
  rw [heq, h3, h2, h1]

theorem fx_data {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K} (P : HS9.Pts91 hc t E φ ψ u) {x : G} (hxM : x ∈ M)
    (hxH : x ∈ H0 M Z) (hx2 : x ^ 2 ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t)
    (hxR : ∀ y ∈ Rt M (LB M Q B) t, x * y * x⁻¹ ∈ Rt M (LB M Q B) t)
    (hsing : ∀ k ∈ Vt M (LB M Q B) B Z t, HS9.IsSingV M Q Z B t ⁅x, k⁆ → ⁅x, k⁆ ∈ Z)
    (hne : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z) :
    ∃ Fx : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K),
      (∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = x * k * x⁻¹ →
        Fx (secVec ψ k) = secVec ψ k') ∧
      (∀ w, Fx (Fx w) = w) ∧ (∀ v, quadPlus 2 K (Fx v) = quadPlus 2 K v) ∧
      (∃ v, Fx v ≠ v) ∧ (∀ v, quadPlus 2 K (Fx v + v) = 0 → Fx v + v = 0) := by
  classical
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
  have hneg : ∀ v : Fin 2 ⊕ Fin 2 → K, -v = v := fun v => by
    ext i
    simp [CharTwo.neg_eq]
  have hFne : ∃ v, Fx v ≠ v := by
    obtain ⟨v₀, hv₀, hv₀Z⟩ := hne
    refine ⟨secVec ψ ⟨v₀, hv₀⟩, fun h => hv₀Z ?_⟩
    have hk : Fx (secVec ψ ⟨v₀, hv₀⟩) = secVec ψ ⟨x * v₀ * x⁻¹, hxV v₀ hv₀⟩ :=
      hFx ⟨v₀, hv₀⟩ ⟨x * v₀ * x⁻¹, hxV v₀ hv₀⟩ rfl
    rw [hk] at h
    have := (secVec_eq_iff ψ ⟨x * v₀ * x⁻¹, hxV v₀ hv₀⟩ ⟨v₀, hv₀⟩).mp h
    simpa [commutatorElement_def, mul_assoc] using this
  have hns : ∀ v, quadPlus 2 K (Fx v + v) = 0 → Fx v + v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ v
    let k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k * x⁻¹, hxV k k.2⟩
    let cV : ↥(Vt M (LB M Q B) B Z t) :=
      ⟨⁅x, (k : G)⁆, (Vt M (LB M Q B) B Z t).mul_mem (hxV k k.2)
        ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩
    have hFk : Fx (secVec ψ k) = secVec ψ k₁ := hFx k k₁ rfl
    have hcv : secVec ψ cV = Fx (secVec ψ k) + secVec ψ k := by
      rw [hFk]
      have e : cV = k₁ * k⁻¹ := Subtype.ext (by simp [cV, k₁, commutatorElement_def, mul_assoc])
      rw [e, secVec_mul, secVec_inv, hneg]
    have hQw : quadPlus 2 K (secVec ψ cV) = 0 := by
      rw [hcv]
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
  exact ⟨Fx, hFx, hFFx, iso, hFne, hns⟩

theorem exists_adjust (h34 : Stroth34Statement) (hCentre : Step95CentreStatement)
    (h1 : Step93OneStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G}
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hsc : StronglyClosedMod M Z0 (LB M Q B)) {s z : G} (hT : Sec9T1 M Q Z0 s z)
    (hne : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∉ Z) :
    ∃ g ∈ Rt M (LB M Q B) t,
      conjSubgroup (g * z * s * (g * z)⁻¹) B ≤ conjSubgroup r B ⊔ Z ∧
      conjSubgroup (g * z * s * (g * z)⁻¹) (conjSubgroup r B) ≤ B ⊔ Z := by
  classical
  obtain ⟨hxM, hxH, hx2, hxVeq⟩ := x_facts hCentre hs hZ0 hT
  have ht : t ∈ LB M Q B := hs.mem
  have hxRe := conj_Rt_of_one h1 hs hr hZ0 hsc hxM hxVeq
  set x := z * s * z⁻¹ with hx
  set V := Vt M (LB M Q B) B Z t with hV
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxVeq) v).mp hv
  have hxR : ∀ y ∈ Rt M (LB M Q B) t, x * y * x⁻¹ ∈ Rt M (LB M Q B) t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxRe) y).mp hy
  have hsing : ∀ k ∈ V, HS9.IsSingV M Q Z B t ⁅x, k⁆ → ⁅x, k⁆ ∈ Z := by
    intro k hk hsk
    have hkV : ⁅x, k⁆ ∈ V := V.mul_mem (hxV k hk) (V.inv_mem hk)
    exact notSing_inf_conj h1 hCentre hs hr hZ0 hsc hT _
      ⟨hkV, comm_mem_conj_Vt hCentre hs hZ0 hT hk⟩ hsk
  obtain ⟨K, fK, finK, chK, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  obtain ⟨Fx, hFx, hFFx, iso, hFne, hns⟩ := fx_data hs P hxM hxH hx2 hxV hxR hsing hne
  obtain ⟨c, hc0, hFxform⟩ := exists_reflection_form (quadPlus 2 K) Fx iso hFFx hFne hns
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hBV : B ≤ V := hc.B_le_Vt ht
  have hφrX : (φ ⟨r, hrR⟩ : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadPlus 2 K) :=
    P.range ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
  set a : Fin 2 ⊕ Fin 2 → K :=
    ((φ ⟨r, hrR⟩ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u
    with ha
  have haQ : quadPlus 2 K a = 0 := by
    rw [ha, E.quad_mulVec hφrX]
    exact P.sing
  have hua : QuadraticMap.polar (quadPlus 2 K) u a ≠ 0 :=
    (HS9.hypPlane_iff_polar91 h34 hs P ⟨r, hrR⟩).mp hr.plane
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  obtain ⟨A, hA, μ, hμ0, hAμ⟩ := exists_mem_conj_reflection_apply (quadPlus 2 K)
    (StatedOmega (StatedQuadPlus 2 K)) (fun A hA v => E.quad_mulVec hA v)
    (fun x y hx hy hxy => E.exists_mulVec_eq hQnd (P := plusPair K 0) (P' := plusPair K 1)
      (plusPair_orth (by decide)) hx hy hxy) c u a hc0 P.sing haQ hua
  have hefun : (fun v => v + (QuadraticMap.polar (quadPlus 2 K) v c / quadPlus 2 K c) • c) =
      Fx := funext fun v => (hFxform v).symm
  rw [hefun] at hAμ
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (P.range ▸ hA)
  have hAA : ∀ v, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hAA' : ∀ v, (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hback : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Fx (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a) =
        μ⁻¹ • u := by
    have h1' := congrArg (fun w => ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w) hAμ
    simp only [hAA', Matrix.mulVec_smul] at h1'
    have h2' := congrArg Fx h1'
    rw [hFFx, map_smul] at h2'
    have h3' := congrArg (fun w => (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w) h2'
    simp only [hAA, Matrix.mulVec_smul] at h3'
    calc (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Fx (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a)
        = μ⁻¹ • (μ • ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Fx (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a))) :=
          by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • u := by rw [← h3']
  have hx'eq : (g : G) * z * s * ((g : G) * z)⁻¹ = (g : G) * x * (g : G)⁻¹ := by
    simp only [hx]
    group
  have hx'V : ∀ v ∈ V, (g : G) * x * (g : G)⁻¹ * v * ((g : G) * x * (g : G)⁻¹)⁻¹ ∈ V := by
    intro v hv
    have h1 : (g : G)⁻¹ * v * (g : G) ∈ V := by
      have := hVR ((g⁻¹ : ↥(Rt M (LB M Q B) t)) : G) (g⁻¹).2 v hv
      simpa using this
    have h2 := hxV _ h1
    have h3 := hVR g g.2 _ h2
    have e : (g : G) * (x * ((g : G)⁻¹ * v * (g : G)) * x⁻¹) * (g : G)⁻¹ =
        (g : G) * x * (g : G)⁻¹ * v * ((g : G) * x * (g : G)⁻¹)⁻¹ := by group
    rwa [e] at h3
  refine ⟨g, g.2, ?_, ?_⟩
  · rw [hx'eq]
    rintro y ⟨b, hb, rfl⟩
    show (g : G) * x * (g : G)⁻¹ * b * ((g : G) * x * (g : G)⁻¹)⁻¹ ∈ conjSubgroup r B ⊔ Z
    set bV : ↥V := ⟨b, hBV hb⟩ with hbV
    obtain ⟨lam, hlam⟩ := (P.point (secVec ψ bV)).mp ⟨bV, hb, rfl⟩
    have hyV := hx'V b (hBV hb)
    have hvec := secVec_conj_conj (hc := hc) ht φ ψ P.act hxV Fx hFx g bV hyV
    rw [hg, hlam] at hvec
    have hvec' : secVec ψ ⟨(g : G) * x * (g : G)⁻¹ * b * ((g : G) * x * (g : G)⁻¹)⁻¹, hyV⟩ =
        (lam * μ) • a := by
      rw [hvec, Matrix.mulVec_smul, map_smul, Matrix.mulVec_smul, hAμ, smul_smul]
    obtain ⟨b', hb'B, hb's⟩ := (P.point ((lam * μ) • u)).mpr ⟨lam * μ, rfl⟩
    have hrb : (r : G) * (b' : G) * (r : G)⁻¹ ∈ V := hVR r hrR b' b'.2
    have hrvec : secVec ψ ⟨(r : G) * (b' : G) * (r : G)⁻¹, hrb⟩ = (lam * μ) • a := by
      have h : secVec ψ ⟨(r : G) * (b' : G) * (r : G)⁻¹, hrb⟩ =
          (φ ⟨r, hrR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ b' :=
        P.act ⟨r, hrR⟩ b' ⟨(r : G) * (b' : G) * (r : G)⁻¹, hrb⟩ rfl
      rw [h, hb's, Matrix.mulVec_smul]
    exact mem_of_secVec_eq (S := conjSubgroup r B ⊔ Z) le_sup_right ψ
      (w := ⟨(r : G) * (b' : G) * (r : G)⁻¹, hrb⟩)
      (Subgroup.mem_sup_left (conj_mem' r hb'B)) (hrvec.trans hvec'.symm)
  · rw [hx'eq]
    rintro y ⟨w, hw, rfl⟩
    show (g : G) * x * (g : G)⁻¹ * w * ((g : G) * x * (g : G)⁻¹)⁻¹ ∈ B ⊔ Z
    have hb₀ : (r : G)⁻¹ * w * (r : G) ∈ B := mem_conjSubgroup.mp hw
    set b₀V : ↥V := ⟨(r : G)⁻¹ * w * (r : G), hBV hb₀⟩ with hb₀V
    obtain ⟨lam, hlam⟩ := (P.point (secVec ψ b₀V)).mp ⟨b₀V, hb₀, rfl⟩
    have hwV : w ∈ V := by
      have := hVR r hrR _ (hBV hb₀)
      simpa [mul_assoc] using this
    set wV : ↥V := ⟨w, hwV⟩ with hwVdef
    have hwvec : secVec ψ wV = lam • a := by
      have h : secVec ψ wV = (φ ⟨r, hrR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          secVec ψ b₀V := P.act ⟨r, hrR⟩ b₀V wV (by simp [hwVdef, hb₀V, mul_assoc])
      rw [h, hlam, Matrix.mulVec_smul]
    have hyV := hx'V w hwV
    have hvec := secVec_conj_conj (hc := hc) ht φ ψ P.act hxV Fx hFx g wV hyV
    rw [hg, hwvec] at hvec
    have hvec' : secVec ψ ⟨(g : G) * x * (g : G)⁻¹ * w * ((g : G) * x * (g : G)⁻¹)⁻¹, hyV⟩ =
        (lam * μ⁻¹) • u := by
      rw [hvec, Matrix.mulVec_smul, map_smul, Matrix.mulVec_smul, hback, smul_smul]
    obtain ⟨b'', hb''B, hb''s⟩ := (P.point ((lam * μ⁻¹) • u)).mpr ⟨lam * μ⁻¹, rfl⟩
    exact mem_of_secVec_eq (S := B ⊔ Z) le_sup_right ψ (w := b'')
      (Subgroup.mem_sup_left hb''B) (hb''s.trans hvec'.symm)

end HS93


theorem step93VanishCount_of_claims (h34 : Stroth34Statement) (hCentre : Step95CentreStatement)
    (h1 : Step93OneStatement) (h91b : Stroth91bStatement) : Step93VanishCountStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT hne
  obtain ⟨g, hg, hsw1, hsw2⟩ := HS93.exists_adjust h34 hCentre h1 hs hr hZ0 hsc hT hne
  have hgM : g ∈ M := hc.Rt_le_M t hg
  have ht : t ∈ LB M Q B := hs.mem
  have hxe : g * z * s * (g * z)⁻¹ = g * (z * s * z⁻¹) * g⁻¹ := by group
  have hgZ0 : ∀ y ∈ Z0, g⁻¹ * y * g ∈ Z0 := fun y hy => by
    have := HS93.conj_mem_Z0 (hc := hc) hZ0 ((Rt M (LB M Q B) t).inv_mem hg) hy
    simpa using this
  have hT' : Sec9T1 M Q Z0 s (g * z) := by
    refine ⟨hT.s_mem, M.mul_mem hgM hT.z_mem, fun y hy => ?_, fun hx => hT.not_mem ?_⟩
    · rw [hxe]
      have h2 := hT.comm _ (hgZ0 y hy)
      have e : ⁅g * (z * s * z⁻¹) * g⁻¹, y⁆ = g * ⁅z * s * z⁻¹, g⁻¹ * y * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact HS93.norm_Q hc hgM h2
    · rw [hxe] at hx
      have := HS93.conj_mem_Z0 (hc := hc) hZ0 ((Rt M (LB M Q B) t).inv_mem hg) hx
      simpa [mul_assoc] using this
  have hne' : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅g * z * s * (g * z)⁻¹, v⁆ ∉ Z := by
    obtain ⟨v, hv, hvZ⟩ := hne
    have hgv : g * v * g⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hg) v).mp hv
    refine ⟨g * v * g⁻¹, hgv, fun hmem => hvZ ?_⟩
    have e : ⁅g * z * s * (g * z)⁻¹, g * v * g⁻¹⁆ = g * ⁅z * s * z⁻¹, v⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e] at hmem
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hgM)) _).mp hmem
    simpa [mul_assoc] using this
  exact HS93.count_core hCentre h91b hs hr hZ0 hT' hne' hsw1 hsw2

theorem step93VanishCount_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) : Step93VanishCountStatement :=
  step93VanishCount_of_claims h34 (step95Centre_of h34 h311a h311bComm h311bCard)
    (step93One_of h34 h311a h311bComm h312b)
    (stroth91b_of_steps h34 h311a (sec9NComm_of_311b h34 h311bComm) (step91OrderQB_of h34)
      (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34))

theorem step93Vanish_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) (h91 : Stroth91Statement) (h92 : Stroth92Statement)
    (hA : Sec9AExistsStatement) : Step93VanishStatement :=
  step93Vanish_of_swap h92
    (step92Nontriv_of h34 hA h91.2.1 (sec9NGeFive_of h34 h311a h311bComm h311bCard)
      (step91OrderQB_of h34) (step91OrderVQB_of h34))
    (sec9NGeFive_of h34 h311a h311bComm h311bCard) (sec95N5_of h34 h91 hA)
    (sec95N6_of h34 h91 (step91OrderVQB_of h34) hA)
    (step95Centre_of h34 h311a h311bComm h311bCard) (step93One_of h34 h311a h311bComm h312b)
    (step93VanishSwap_of h34 h311a h311bComm h311bCard h312b)
    (step93VanishCount_of h34 h311a h311bComm h311bCard h312b)

end CFSG.RankThree.GF2n.Stroth80
