module

public import CFSG.Quasithin.Recognition.St84.Gen.CrossedHomPrincipal
public import CFSG.Quasithin.Recognition.St84.G24Twist
public import CFSG.LocalAnalysis.ComponentInitial.CentralBinaryQuadraticIso

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.St84

variable {G G' : Type*} [Group G] [Group G']

private theorem isElementaryAbelian_of_comm_exp_two {G : Type*} [Group G]
    {Z Q : Subgroup G} (hZQ : Z ≤ Q)
    (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 ↥Z :=
  { toIsMulCommutative :=
      ⟨⟨fun a b => Subtype.ext (hZc (a : G) a.2 (b : G) (hZQ b.2))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun z => by
      apply Subtype.ext
      simpa using hZ2 (z : G) z.2) }

private theorem quotient_elementaryAbelian {G : Type*} [Group G]
    {Q Z : Subgroup G} (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z) [hWn : (Z.subgroupOf Q).Normal] :
    CFSG.IsElementaryAbelian 2 (↥Q ⧸ Z.subgroupOf Q) := by
  have hU2 : ∀ u : ↥Q ⧸ Z.subgroupOf Q, u ^ 2 = 1 := by
    intro u
    induction u using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hQ2 (x : G) x.2
  have hUcomm : ∀ a b : ↥Q ⧸ Z.subgroupOf Q, a * b = b * a := by
    intro a b
    have h1 := hU2 (a * b)
    have h2 := hU2 a
    have h3 := hU2 b
    rw [sq] at h1 h2 h3
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [h2, h3, one_mul, mul_one]
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact ⟨⟨hUcomm⟩⟩
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one hU2

theorem exists_vertexIso_special [Finite G] [Finite G'] {Q R Z : Subgroup G}
    {Q' R' Z' : Subgroup G'}
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (hQR : Disjoint Q R)
    (hR'Q' : R' ≤ Subgroup.normalizer (Q' : Set G')) (hQR' : Disjoint Q' R')
    (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z) (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z)
    (hZQ' : Z' ≤ Q') (hZc' : ∀ z ∈ Z', ∀ x ∈ Q', z * x = x * z) (hZ2' : ∀ z ∈ Z', z ^ 2 = 1)
    (hQ2' : ∀ x ∈ Q', x ^ 2 ∈ Z') (hRZ' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    [hWn : (Z.subgroupOf Q).Normal] [hW'n : (Z'.subgroupOf Q').Normal]
    (e : ↥R ≃* ↥R') (f : ↥Q ⧸ Z.subgroupOf Q ≃* ↥Q' ⧸ Z'.subgroupOf Q') (g : ↥Z ≃* ↥Z')
    (hf : ∀ (r : ↥R) (v w : ↥Q) (v' w' : ↥Q'), (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : G') = (e r : G') * v' * (e r : G')⁻¹ →
        f (QuotientGroup.mk v) = QuotientGroup.mk v' → f (QuotientGroup.mk w) = QuotientGroup.mk w')
    (hg : ∀ (r : ↥R) (z w : ↥Z), (w : G) = (r : G) * z * (r : G)⁻¹ →
      (g w : G') = (e r : G') * (g z : G') * (e r : G')⁻¹)
    (hsq : ∀ (v : ↥Q) (v' : ↥Q'), f (QuotientGroup.mk v) = QuotientGroup.mk v' →
      ∀ hz : (v : G) ^ 2 ∈ Z, (g ⟨(v : G) ^ 2, hz⟩ : G') = (v' : G') ^ 2)
    (hH1 : CrossedHomPrincipal Q Z R Z' R' e) :
    ∃ θ : ↥Q ≃* ↥Q', ∃ ψ : ↥(Q ⊔ R) ≃* ↥(Q' ⊔ R'),
      (∀ v : ↥Q, (ψ ⟨v, Subgroup.mem_sup_left v.2⟩ : G') = θ v) ∧
      (∀ r : ↥R, (ψ ⟨r, Subgroup.mem_sup_right r.2⟩ : G') = e r) ∧
      (∀ v : ↥Q, f (QuotientGroup.mk v) = QuotientGroup.mk (θ v)) ∧
      ∀ z : ↥Z, (θ ⟨z, hZQ z.2⟩ : G') = g z := by
  classical
  let W : Subgroup ↥Q := Z.subgroupOf Q
  let W' : Subgroup ↥Q' := Z'.subgroupOf Q'
  have hWle : W ≤ Subgroup.center ↥Q := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (hZc (w : G) (Subgroup.mem_subgroupOf.mp hw) (x : G) x.2).symm
  have hW'le : W' ≤ Subgroup.center ↥Q' := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (hZc' (w : G') (Subgroup.mem_subgroupOf.mp hw) (x : G') x.2).symm
  have hZel : CFSG.IsElementaryAbelian 2 ↥Z :=
    isElementaryAbelian_of_comm_exp_two hZQ hZc hZ2
  have hZ'el : CFSG.IsElementaryAbelian 2 ↥Z' :=
    isElementaryAbelian_of_comm_exp_two hZQ' hZc' hZ2'
  have hWel : CFSG.IsElementaryAbelian 2 W := CFSG.IsElementaryAbelian.subgroupOf hZQ
  have hW'el : CFSG.IsElementaryAbelian 2 W' := CFSG.IsElementaryAbelian.subgroupOf hZQ'
  have hUel : CFSG.IsElementaryAbelian 2 (↥Q ⧸ W) :=
    quotient_elementaryAbelian hZc hQ2
  have hU'el : CFSG.IsElementaryAbelian 2 (↥Q' ⧸ W') :=
    quotient_elementaryAbelian hZc' hQ2'
  let g' : W ≃* W' :=
    (Subgroup.subgroupOfEquivOfLe hZQ).trans (g.trans (Subgroup.subgroupOfEquivOfLe hZQ').symm)
  have hg'_coe : ∀ (w : W), ((g' w : W') : G') =
      (g ⟨(w : G), Subgroup.mem_subgroupOf.mp w.2⟩ : G') := by
    intro w
    change ((g ((Subgroup.subgroupOfEquivOfLe hZQ) w) : ↥Z') : G') = _
    have harg : (Subgroup.subgroupOfEquivOfLe hZQ) w =
        (⟨(w : G), Subgroup.mem_subgroupOf.mp w.2⟩ : ↥Z) := by
      apply Subtype.ext
      exact Subgroup.subgroupOfEquivOfLe_apply_coe hZQ w
    rw [harg]
  have hsq' : ∀ u : ↥Q ⧸ W,
      g' (squareMap hWle (sq_eq_one_of_elem_sub hWel) (sq_eq_one_of_elem hUel) u) =
        squareMap hW'le (sq_eq_one_of_elem_sub hW'el) (sq_eq_one_of_elem hU'el) (f u) := by
    intro u
    induction u using QuotientGroup.induction_on with | H v => ?_
    obtain ⟨v', hv'⟩ := QuotientGroup.mk_surjective (f (QuotientGroup.mk v))
    have hsqv : ∀ hz : (v : G) ^ 2 ∈ Z, (g ⟨(v : G) ^ 2, hz⟩ : G') = (v' : G') ^ 2 :=
      hsq v v' hv'.symm
    apply Subtype.ext
    apply Subtype.ext
    have hleft : ((g' (squareMap hWle (sq_eq_one_of_elem_sub hWel) (sq_eq_one_of_elem hUel)
          (QuotientGroup.mk v)) : W') : G') =
        (g ⟨(v : G) ^ 2, Subgroup.mem_subgroupOf.mp (sq_mem_of_quotient
          (sq_eq_one_of_elem hUel) v)⟩ : G') := by
      change ((g' ⟨(v : ↥Q) ^ 2, Subgroup.mem_subgroupOf.mpr (by
        simpa using hQ2 (v : G) v.2)⟩ : W') : G') = _
      rw [hg'_coe]
      rfl
    have hright : ((squareMap hW'le (sq_eq_one_of_elem_sub hW'el) (sq_eq_one_of_elem hU'el)
          (f (QuotientGroup.mk v)) : W') : G') = (v' : G') ^ 2 := by
      rw [← hv']
      change (((⟨(v' : ↥Q') ^ 2, Subgroup.mem_subgroupOf.mpr (by
        simpa using hQ2' (v' : G') v'.2)⟩ : W') : G')) = (v' : G') ^ 2
      rfl
    rw [hleft, hright]
    exact hsqv _
  obtain ⟨β₀, hβ₀W, hβ₀f⟩ :=
    (central_binary_extension_quadratic_isomorphism hWle hW'le hWel hW'el hUel hU'el f g').mpr hsq'
  have hβ₀Z : ∀ (v : ↥Q) (hz : (v : G) ∈ Z), (β₀ v : G') = g ⟨(v : G), hz⟩ := by
    intro v hz
    have h := hβ₀W ⟨v, Subgroup.mem_subgroupOf.mpr hz⟩
    have hcoe := congrArg (fun y : ↥Q' => (y : G')) h
    rw [hg'_coe] at hcoe
    simpa using hcoe
  have hβ₀f' : ∀ v : ↥Q, f (QuotientGroup.mk v) = QuotientGroup.mk (β₀ v) := by
    intro v
    have h := hβ₀f v
    change (QuotientGroup.mk (β₀ v) : ↥Q' ⧸ W') = f (QuotientGroup.mk v) at h
    exact h.symm
  let cjQ : ↥R →* MulAut ↥Q := CFSG.GroupTheory.conjHom Q R hRQ
  have hcjQ : ∀ (r : ↥R) (v : ↥Q),
      ((cjQ r) v : G) = (r : G) * (v : G) * (r : G)⁻¹ := fun r v =>
    CFSG.GroupTheory.conjHom_apply hRQ r v
  let cjQ' : ↥R →* MulAut ↥Q' := (CFSG.GroupTheory.conjHom Q' R' hR'Q').comp e
  have hcjQ' : ∀ (r : ↥R) (v : ↥Q'),
      ((cjQ' r) v : G') = (e r : G') * (v : G') * (e r : G')⁻¹ := fun r v =>
    CFSG.GroupTheory.conjHom_apply hR'Q' (e r) v
  have hmemW : ∀ (r : ↥R) (v : ↥Q),
      β₀ (cjQ r v) * ((cjQ' r) (β₀ v))⁻¹ ∈ W' := by
    intro r v
    have hw : ((cjQ r v : ↥Q) : G) = (r : G) * (v : G) * (r : G)⁻¹ := hcjQ r v
    have hfv : f (QuotientGroup.mk v) = QuotientGroup.mk (β₀ v) := hβ₀f' v
    have hfw : f (QuotientGroup.mk (cjQ r v)) =
        QuotientGroup.mk ((cjQ' r) (β₀ v)) :=
      hf r v (cjQ r v) (β₀ v) ((cjQ' r) (β₀ v)) hw (hcjQ' r (β₀ v)) hfv
    have hfw' : f (QuotientGroup.mk (cjQ r v)) =
        QuotientGroup.mk (β₀ (cjQ r v)) := hβ₀f' (cjQ r v)
    have heq : (QuotientGroup.mk (β₀ (cjQ r v)) : ↥Q' ⧸ W') =
        QuotientGroup.mk ((cjQ' r) (β₀ v)) := by
      rw [← hfw', hfw]
    have hmkW : β₀ (cjQ r v) * ((cjQ' r) (β₀ v))⁻¹ ∈ W' := by
      have hmk : (QuotientGroup.mk
          (β₀ (cjQ r v) * ((cjQ' r) (β₀ v))⁻¹) : ↥Q' ⧸ W') = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp hmk
    exact hmkW
  have hmem : ∀ (r : ↥R) (v : ↥Q),
      ((β₀ (cjQ r v) * ((cjQ' r) (β₀ v))⁻¹ : ↥Q') : G') ∈ Z' :=
    fun r v => Subgroup.mem_subgroupOf.mp (hmemW r v)
  have hmul : ∀ (r : ↥R) (v₁ v₂ : ↥Q),
      β₀ (cjQ r (v₁ * v₂)) * ((cjQ' r) (β₀ (v₁ * v₂)))⁻¹ =
        (β₀ (cjQ r v₁) * ((cjQ' r) (β₀ v₁))⁻¹) *
          (β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹) := by
    intro r v₁ v₂
    rw [map_mul (cjQ r), map_mul β₀]
    have hA : (cjQ' r) (β₀ (v₁ * v₂)) =
        (cjQ' r) (β₀ v₁) * (cjQ' r) (β₀ v₂) := by
      rw [map_mul β₀, map_mul (cjQ' r)]
    rw [map_mul β₀, map_mul (cjQ' r)]
    have hA₁mem : (((cjQ' r) (β₀ v₁) : ↥Q') : G') ∈ Q' := ((cjQ' r) (β₀ v₁)).2
    have hZ₂ : ((β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹ : ↥Q') : G') ∈ Z' :=
      hmem r v₂
    have hA₁inv : ((((cjQ' r) (β₀ v₁))⁻¹ : ↥Q') : G') ∈ Q' := Q'.inv_mem hA₁mem
    have hcomm : (β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹) *
        ((cjQ' r) (β₀ v₁))⁻¹ =
        ((cjQ' r) (β₀ v₁))⁻¹ *
          (β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹) := by
      apply Subtype.ext
      exact hZc' _ hZ₂ _ hA₁inv
    calc β₀ (cjQ r v₁) * β₀ (cjQ r v₂) *
          ((cjQ' r) (β₀ v₁) * (cjQ' r) (β₀ v₂))⁻¹
        = β₀ (cjQ r v₁) * β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹ *
            ((cjQ' r) (β₀ v₁))⁻¹ := by rw [mul_inv_rev]; group
      _ = β₀ (cjQ r v₁) *
            ((β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹) *
              ((cjQ' r) (β₀ v₁))⁻¹) := by group
      _ = β₀ (cjQ r v₁) *
            (((cjQ' r) (β₀ v₁))⁻¹ *
              (β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹)) := by rw [hcomm]
      _ = (β₀ (cjQ r v₁) * ((cjQ' r) (β₀ v₁))⁻¹) *
            (β₀ (cjQ r v₂) * ((cjQ' r) (β₀ v₂))⁻¹) := by group
  let δ (r : ↥R) : ↥Q →* ↥Z' :=
    MonoidHom.mk' (fun v => (⟨β₀ (cjQ r v) * ((cjQ' r) (β₀ v))⁻¹, hmem r v⟩ : ↥Z'))
      (fun v₁ v₂ => by
        apply Subtype.ext
        exact congrArg (fun x : ↥Q' => (x : G')) (hmul r v₁ v₂))
  have hδ_coe : ∀ (r : ↥R) (v : ↥Q),
      ((δ r v : ↥Z') : G') = β₀ (cjQ r v) * ((cjQ' r) (β₀ v))⁻¹ := fun r v => rfl
  have hZδ : ∀ (r : ↥R) (v : ↥Q), (v : G) ∈ Z → δ r v = 1 := by
    intro r v hv
    apply Subtype.ext
    rw [hδ_coe]
    have hwZ : ((cjQ r v : ↥Q) : G) ∈ Z := by
      rw [hcjQ r v]
      exact hRZ (r : G) r.2 (v : G) hv
    have hβw : (β₀ (cjQ r v) : G') = g ⟨((cjQ r v : ↥Q) : G), hwZ⟩ := hβ₀Z _ hwZ
    have hβv : (β₀ v : G') = g ⟨(v : G), hv⟩ := hβ₀Z v hv
    have hgw : (g ⟨((cjQ r v : ↥Q) : G), hwZ⟩ : G') =
        (e r : G') * (g ⟨(v : G), hv⟩ : G') * (e r : G')⁻¹ :=
      hg r ⟨v, hv⟩ ⟨cjQ r v, hwZ⟩ (hcjQ r v)
    change (β₀ (cjQ r v) : G') * (((cjQ' r) (β₀ v) : ↥Q') : G')⁻¹ = 1
    rw [hβw, hcjQ' r (β₀ v), hβv, hgw]
    group
  have hcjQ_mul : ∀ (r s : ↥R) (v : ↥Q), cjQ (r * s) v = cjQ r (cjQ s v) := by
    intro r s v
    rw [map_mul]
    rfl
  have hcjQ'_mul : ∀ (r s : ↥R) (v : ↥Q'), (cjQ' (r * s)) v = (cjQ' r) ((cjQ' s) v) := by
    intro r s v
    rw [map_mul]
    rfl
  have hcoc : ∀ (r s : ↥R) (v w : ↥Q), (w : G) = (s : G) * v * (s : G)⁻¹ →
      ((δ (r * s) v : ↥Z') : G') =
        (δ r w : G') * ((e r : G') * (δ s v : G') * (e r : G')⁻¹) := by
    intro r s v w hw
    have hw' : w = cjQ s v := by
      apply Subtype.ext
      rw [hcjQ s v, hw]
    rw [hw']
    rw [hδ_coe (r * s) v, hδ_coe r (cjQ s v), hδ_coe s v]
    rw [hcjQ_mul, hcjQ'_mul]
    simp only [Subgroup.coe_inv]
    rw [hcjQ' r ((cjQ' s) (β₀ v)), hcjQ' r (β₀ (cjQ s v)), hcjQ' s (β₀ v)]
    group
  obtain ⟨φ, hφZ, hφR⟩ := hH1 δ hZδ hcoc
  have hβZ : ∀ v : ↥Q, (v : G) ∈ Z ↔ (β₀ v : G') ∈ Z' := by
    intro v
    constructor
    · intro hv
      rw [hβ₀Z v hv]
      exact (g ⟨(v : G), hv⟩).2
    · intro hv
      have hmk : f (QuotientGroup.mk v) = 1 := by
        rw [hβ₀f' v, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hv
      have hmkv : (QuotientGroup.mk v : ↥Q ⧸ W) = 1 := by
        apply f.injective
        rw [hmk, map_one]
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff v).mp hmkv)
  have hcob : ∀ (a : ↥R) (v w : ↥Q), (w : G) = (a : G) * (v : G) * (a : G)⁻¹ →
      (β₀ w : G') * ((e a : G') * (β₀ v : G') * (e a : G')⁻¹)⁻¹ =
        (φ w : G') * ((e a : G') * (φ v : G') * (e a : G')⁻¹)⁻¹ := by
    intro a v w hw
    have hw' : w = cjQ a v := by
      apply Subtype.ext
      rw [hcjQ a v, hw]
    have h := hφR a a.2 v w hw
    have hδa : ((δ a v : ↥Z') : G') =
        (β₀ w : G') * ((e a : G') * (β₀ v : G') * (e a : G')⁻¹)⁻¹ := by
      rw [hδ_coe, hw']
      simp only [Subgroup.coe_inv, hcjQ' a (β₀ v)]
    rw [hδa] at h
    exact h
  obtain ⟨θ, hθ_eq, hθZ, hθeq⟩ :=
    exists_equivariant_twist hZQ' hZc' hRZ' β₀ e hβZ φ hφZ hcob
  obtain ⟨ψ, hψQ, hψR⟩ :=
    exists_mulEquiv_sup_extend hRQ hQR hR'Q' hQR' θ e
      (fun k q hq => hθeq k q ⟨(k : G) * (q : G) * (k : G)⁻¹, hq⟩ rfl)
  refine ⟨θ, ψ, hψQ, hψR, ?_, ?_⟩
  · intro v
    let zφ : ↥Q' := ⟨(φ v : G'), hZQ' (φ v).2⟩
    have hzφW : zφ ∈ W' := Subgroup.mem_subgroupOf.mpr (φ v).2
    have hzφmk : (QuotientGroup.mk zφ : ↥Q' ⧸ W') = 1 :=
      (QuotientGroup.eq_one_iff zφ).mpr hzφW
    have hθsub : θ v = β₀ v * zφ⁻¹ := by
      apply Subtype.ext
      simpa [zφ] using hθ_eq v
    calc f (QuotientGroup.mk v) = QuotientGroup.mk (β₀ v) := hβ₀f' v
      _ = QuotientGroup.mk (β₀ v * zφ⁻¹) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hzφmk, inv_one, mul_one]
      _ = QuotientGroup.mk (θ v) := by rw [hθsub]
  · intro z
    have hβZeq : θ ⟨z, hZQ z.2⟩ = β₀ ⟨z, hZQ z.2⟩ := hθZ _ (by simpa using z.2)
    calc (θ ⟨z, hZQ z.2⟩ : G') = (β₀ ⟨z, hZQ z.2⟩ : G') := by rw [hβZeq]
      _ = (g ⟨(z : G), z.2⟩ : G') := hβ₀Z ⟨z, hZQ z.2⟩ (by simpa using z.2)
      _ = (g z : G') := rfl

end CFSG.Quasithin.F112R.St84

end
