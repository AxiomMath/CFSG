module

public import CFSG.RankThree.GF2n.Smith81.Orth213Stmts
public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIBasic
public import CFSG.RankThree.GF2n.Smith81.Orth213LemmaQ
public import CFSG.RankThree.GF2n.Smith81.Orth213OddGroup

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (eichler)
open scoped commutatorElement

namespace Orth213

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem ne_bot_QB (hc : SmithOrthCfg M Q Z B) (h28 : Smith28OrthStatement) {X : Subgroup G}
    {x : G} (hs : Sit M Q Z X x) : Q ⊓ QB X ≠ ⊥ := by
  obtain ⟨v, hv, hvQ, hvX⟩ := h28 G M Q Z B hc X x hs
  intro h
  have hm : v ∈ Q ⊓ QB X := ⟨hvQ, hvX⟩
  rw [h, Subgroup.mem_bot] at hm
  exact ne_one_of_isConj_Z hs.ne_one hv hm

theorem orthTensor_neg {K ι : Type} [Field K] (g : Matrix (Fin 2) (Fin 2) K)
    (o : (ι → K) ≃ₗ[K] (ι → K)) (w : (ι → K) × (ι → K)) :
    orthTensor g o (-w) = -orthTensor g o w := by
  refine Prod.ext ?_ ?_ <;>
    simp only [orthTensor, Prod.fst_neg, Prod.snd_neg, map_neg, smul_neg] <;> abel

theorem exists_root_group_centralizer (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (h28 : Smith28OrthStatement) (h4 : Orth212C4CondStatement) (h5 : Orth212C5CondStatement)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {X Y : Subgroup G} {x y : G}
    (hsx : Sit M Q Z X x) (hsy : Sit M Q Z Y y)
    {gx gy : Matrix (Fin 2) (Fin 2) C.K} {ox oy : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hax : ActsAsTensor Q Z C.M₀ C.φ x gx ox) (hay : ActsAsTensor Q Z C.M₀ C.φ y gy oy)
    {w : (C.ι → C.K) × (C.ι → C.K)}
    (hvy : orthTensor gy oy (orthTensor gx ox w - w) = orthTensor gx ox w - w)
    (hpure : PairTypeA C.qU (orthTensor gx ox w - w)) :
    ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ⊓ QB X ∧
      A ≤ Subgroup.centralizer ({y} : Set G) := by
  set v := orthTensor gx ox w - w with hv
  have H := hc.ctx.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨y₀, hy₀Q, hy₀⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) v
  have hy₀c : y₀ ∈ ⁅Q, Subgroup.zpowers x⁆ := by
    refine OrthCaseI.mem_comm_of_range hc C hsx hax hy₀Q (p' := -w) ?_
    rw [hy₀, orthTensor_neg, hv]
    abel
  have hne := ne_bot_QB hc h28 hsx
  have hy₀D : y₀ ∈ (Q ⊓ QB X) ⊔ Z := by
    rw [h5 G M Q Z B hc X x hsx hne]
    exact Subgroup.mem_sup_left hy₀c
  have hDN : (Q ⊓ QB X) ≤ Subgroup.normalizer (Z : Set G) :=
    fun d hd => H.Z_normal.2 (H.Q_normal.1 hd.1)
  obtain ⟨d, hd, z', hz', hdz⟩ := exists_mul_of_mem_sup_of_le_normalizer hDN hy₀D
  have hdQ : d ∈ Q := hd.1
  have hπd : C.M₀.π d = C.M₀.π y₀ := by
    rw [← hdz, C.M₀.π_mul d hdQ z' (hZQ hz'), (C.M₀.π_ker z' (hZQ hz')).mpr hz', add_zero]
  have hφd : C.φ (C.M₀.π d) = v := by rw [hπd]; exact hy₀
  have hv0 : v ≠ 0 := OrthEps.pairTypeA_ne_zero hpure
  have hdZ : d ∉ Z := by
    intro hdZ
    apply hv0
    rw [← hφd, (C.M₀.π_ker d hdQ).mpr hdZ, map_zero]
  have hd1 : d ≠ 1 := fun h => hdZ (h ▸ Z.one_mem)
  have hdc : IsConj z d := (C.hF.root z hz hz1 d hdQ hdZ).mpr (hφd ▸ hpure)
  obtain ⟨A, hA, hdA⟩ := exists_isZConjugate_mem hz hdc
  have hX : IsZConjugate Z X := hsx.conj
  have hAQ : A ≤ Q := by
    have := IsZConjugate.le_QB_of_mem H (IsZConjugate.self Z) hA hd1 hdA
      (by rw [H.QB_Z]; exact hdQ)
    rwa [H.QB_Z] at this
  have hAX : A ≤ QB X := IsZConjugate.le_QB_of_mem H hX hA hd1 hdA hd.2
  have hAZ : A ≠ Z := fun h => hdZ (h ▸ hdA)
  have hcA : Ctx M Q Z A := ⟨H, hA, hAQ, hAZ⟩
  refine ⟨A, hA, le_inf hAQ hAX, ?_⟩
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases ha1 : a = 1
  · rw [ha1]; simp
  have haQ : a ∈ Q := hAQ ha
  have hline := isLineGen_pi hcA C.hD hdA hd1
  obtain ⟨s, hs⟩ := (hline (C.M₀.π a)).mp (C.M₀.pi_mem_img ha haQ)
  have hφa : C.φ (C.M₀.π a) = s • v := by rw [hs, map_smul, hφd]
  have hfix : orthTensor gy oy (C.φ (C.M₀.π a)) = C.φ (C.M₀.π a) := by
    rw [hφa]
    have : orthTensor gy oy (s • v) = s • orthTensor gy oy v :=
      (orthTensorLin gy (oy : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K))).map_smul s v
    rw [this, hvy]
  have hcomm : ⁅a, y⁆ ∈ Z := (OrthCaseI.comm_mem_Z_iff hc C hsy hay haQ).mpr hfix
  have hneY := ne_bot_QB hc h28 hsy
  have hyZ : y * ⁅a, y⁆ * y⁻¹ = ⁅a, y⁆ := hsy.x_cent (smith_1_12 hsy) _ hcomm
  have hconj : IsConj y (y * ⁅a, y⁆) := by
    refine isConj_iff.mpr ⟨a, ?_⟩
    have h1 : y * ⁅a, y⁆ = ⁅a, y⁆ * y := by
      calc y * ⁅a, y⁆ = (y * ⁅a, y⁆ * y⁻¹) * y := by group
        _ = ⁅a, y⁆ * y := by rw [hyZ]
    rw [h1]
    simp only [commutatorElement_def]
    group
  have h1 := h4 G M Q Z B hc Y y hsy hneY _ hcomm hconj
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

section Coordinates

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup V] [Module K V]

@[expose] def conjEquiv (φ : E ≃ₗ[K] V) : (E ≃ₗ[K] E) ≃* (V ≃ₗ[K] V) where
  toFun f := φ.symm.trans (f.trans φ)
  invFun g := φ.trans (g.trans φ.symm)
  left_inv f := by ext e; simp
  right_inv g := by ext v; simp
  map_mul' f g := by ext v; simp

theorem conjEquiv_apply (φ : E ≃ₗ[K] V) (f : E ≃ₗ[K] E) (v : V) :
    conjEquiv φ f v = φ (f (φ.symm v)) := rfl

theorem conjEquiv_apply_φ (φ : E ≃ₗ[K] V) (f : E ≃ₗ[K] E) (e : E) :
    conjEquiv φ f (φ e) = φ (f e) := by
  rw [conjEquiv_apply, LinearEquiv.symm_apply_apply]

end Coordinates

end Orth213

open Orth213

theorem orth213Odd_of (h24 : Smith24ActStatement)
    (hK : OrthClassStatement) (h28 : Smith28OrthStatement) (h4 : Orth212C4CondStatement)
    (h7 : Orth212C7CondStatement) (h5 : Orth212C5CondStatement) : Orth213OddStatement := by
  intro G _ _ M Q Z B hc z hz hz1 x y hxM hyM hxz hyz hxQ hyQ X hX hxX hnoroot
  have H := hc.ctx.hyp
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  have hsx : Sit M Q Z X x := ⟨H, hX, hxX, ne_one_of_isConj_Z hz1 hxz, hxM, hxQ⟩
  obtain ⟨Y, hY, hyY⟩ := exists_isZConjugate_mem hz hyz
  have hsy : Sit M Q Z Y y := ⟨H, hY, hyY, ne_one_of_isConj_Z hz1 hyz, hyM, hyQ⟩
  have hxH : x ∈ H0 M Z := (smith_1_12 hsx).1 hxX
  have hyH : y ∈ H0 M Z := (smith_1_12 hsy).1 hyY
  obtain ⟨ρ, hρπ, hρker, -⟩ := exists_actionHom_H0 H C.hD
  have hactρ : ∀ (m : ↥(H0 M Z)) {g : Matrix (Fin 2) (Fin 2) C.K}
      {o : (C.ι → C.K) → (C.ι → C.K)}, ActsAsTensor Q Z C.M₀ C.φ (m : G) g o →
      ∀ p, conjEquiv C.φ (ρ m) p = orthTensor g o p := by
    intro m g o hact p
    obtain ⟨q, hq, hπ⟩ := C.M₀.π_surj (C.φ.symm p)
    rw [conjEquiv_apply, ← hπ, ← hρπ m q hq, hact q hq, hπ, LinearEquiv.apply_symm_apply]
  have hcls : ∀ {X' : Subgroup G} {m : G}, Sit M Q Z X' m →
      ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)),
        ActsAsTensor Q Z C.M₀ C.φ m g o ∧
        (ClassE (K := C.K) (ι := C.ι) (orthTensor g ⇑o) ∨ ClassA C.qU (orthTensor g ⇑o)) := by
    intro X' m hs
    rcases hK G M Q Z B hc C X' m hs with ⟨g, hdet, hne, hsq, hact⟩ |
        ⟨u, w, hu, hw, huw, hli, hact⟩
    · exact ⟨g, LinearEquiv.refl _ _, hact, Or.inl ⟨g, hdet, hne, hsq, fun p => rfl⟩⟩
    · exact ⟨1, eichler C.qU u w, hact, Or.inr ⟨u, w, hu, hw, huw, hli, fun p => rfl⟩⟩
  obtain ⟨gx, ox, hax, hclx⟩ := hcls hsx
  obtain ⟨gy, oy, hay, hcly⟩ := hcls hsy
  set a : ↥(H0 M Z) := ⟨x, hxH⟩ with ha
  set b : ↥(H0 M Z) := ⟨y, hyH⟩ with hb
  have hXa : ∀ p, conjEquiv C.φ (ρ a) p = orthTensor gx ox p := hactρ a hax
  have hYb : ∀ p, conjEquiv C.φ (ρ b) p = orthTensor gy oy p := hactρ b hay
  have hXfun : (⇑(conjEquiv C.φ (ρ a)) : _ → _) = orthTensor gx ⇑ox := funext hXa
  have hYfun : (⇑(conjEquiv C.φ (ρ b)) : _ → _) = orthTensor gy ⇑oy := funext hYb
  have hX' : ClassE (K := C.K) (ι := C.ι) (conjEquiv C.φ (ρ a)) ∨
      ClassA C.qU (conjEquiv C.φ (ρ a)) := by rw [hXfun]; exact hclx
  have hY' : ClassE (K := C.K) (ι := C.ι) (conjEquiv C.φ (ρ b)) ∨
      ClassA C.qU (conjEquiv C.φ (ρ b)) := by rw [hYfun]; exact hcly
  have hsing : ∃ p : C.ι → C.K, p ≠ 0 ∧ C.qU p = 0 := by
    obtain ⟨v, hv, hvQ, hvX⟩ := h28 G M Q Z B hc X x hsx
    have hvZ : v ∉ Z := by
      intro hvZ
      have hm : v ∈ Z ⊓ QB X := ⟨hvZ, hvX⟩
      rw [Z_inf_QB_eq_bot hsx (smith_1_12 hsx), Subgroup.mem_bot] at hm
      exact ne_one_of_isConj_Z hsx.ne_one hv hm
    obtain ⟨c₁, c₂, u, -, hu, hqu, -⟩ := (C.hF.root z hz hz1 v hvQ hvZ).mp (hxz.trans hv)
    exact ⟨u, hu, hqu⟩
  rcases lemmaQ C.qU C.hF.nondeg hsing (conjEquiv C.φ (ρ a)) (conjEquiv C.φ (ρ b)) hX' hY' with
    ⟨v, hvR, hvy, hvp⟩ | ⟨k, hk, hkpow, hkint⟩
  ·
    exfalso
    obtain ⟨w, hw⟩ := hvR
    have hvw : v = orthTensor gx ox w - w := by
      rw [← hw]
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, hXa]
    rw [hYb] at hvy
    rw [hvw] at hvy hvp
    obtain ⟨A, hA, hAle, hAy⟩ := exists_root_group_centralizer hc C h28 h4 h5 hz hz1 hsx hsy
      hax hay hvy hvp
    exact hnoroot A hA hAle hAy
  ·
    refine odd_orderOf_mul_of_actions (a := a) (b := b) hc h28 h4 h7 ρ hρπ hρker hsx hsy
      ⟨k, hk, ?_⟩ ?_
    · have h1 : conjEquiv C.φ ((ρ a * ρ b) ^ k) = 1 := by
        rw [map_pow, map_mul]
        exact hkpow
      exact (conjEquiv C.φ).injective (h1.trans (map_one _).symm)
    · intro e he hfix
      obtain ⟨e', he'⟩ := he
      apply C.φ.injective
      rw [map_zero]
      refine hkint (C.φ e) ⟨C.φ e', ?_⟩ ?_
      · simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
          conjEquiv_apply_φ]
        rw [← map_sub, ← he']
        rfl
      · rw [← map_mul, conjEquiv_apply_φ, hfix]

end CFSG.RankThree.GF2n.Smith81
