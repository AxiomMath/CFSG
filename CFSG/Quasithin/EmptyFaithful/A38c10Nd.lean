module

public import CFSG.Quasithin.EmptyFaithful.A38c10Mat
public import CFSG.Quasithin.Background.FLc3Pos

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

section Vectors

variable {V : Type} [CommGroup V]

theorem fix_reflection_nd {n : ℕ} {ρ : SLt n →* MulAut V} {U₁ U₂ : Subgroup V} (hdis : U₁ ⊓ U₂ = ⊥)
    (D₁ : VModel n ρ U₁ ⊥ (Multiplicative (Vt n)) (fun g a => actM g a))
    (D₂ : VModel n ρ U₂ ⊥ (Multiplicative (Vt n)) actDl) (hV2 : ∀ w : V, w ^ 2 = 1) (hn : 1 ≤ n)
    (g : SLt n) {v : V} (hv : v ∈ U₁ ⊔ U₂) (hvf : ∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v) {i : ℕ}
    (hi : IsNode n i) (hi1 : i ≠ 1) (hin : i ≠ n - 1) :
    (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v := by
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.1 hv
  have hcomp : ∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v₁ = v₁ ∧ (ρ (g * s * g⁻¹)) v₂ = v₂ := fun s hs =>
    fixed_of_two hdis (ρ (g * s * g⁻¹)) (fun u hu => D₁.inv _ u hu) (fun u hu => D₂.inv _ u hu) hv₁ hv₂
      (hvf s hs)
  rw [map_mul,
    D₁.fix_reflection_conj hV2 hn (c := 1) (fun a ha i hi hic => fix_nat a ha i hi hic) g hv₁
      (fun s hs => (hcomp s hs).1) hi hi1,
    D₂.fix_reflection_conj hV2 hn (c := n - 1) (fun a ha i hi hic => fix_dual hn a ha i hi hic) g hv₂
      (fun s hs => (hcomp s hs).2) hi hin]

theorem fix_reflection_of_models {n : ℕ} {ρ : SLt n →* MulAut V} {U U₁ U₂ : Subgroup V}
    (hsup : U₁ ⊔ U₂ = U) (hdis : U₁ ⊓ U₂ = ⊥)
    (D₁ : VModel n ρ U₁ ⊥ (Multiplicative (Vt n)) (fun g a => actM g a))
    (D₂ : VModel n ρ U₂ ⊥ (Multiplicative (Vt n)) actDl) (hV2 : ∀ w : V, w ^ 2 = 1) (hn : 1 ≤ n) :
    ∀ g : SLt n, ∀ v ∈ U, (∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v) →
      ∀ i, ∀ hi : IsNode n i, i ∈ {j : ℕ | j ≠ 1 ∧ j ≠ n - 1} →
        (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v := by
  intro g v hv hvf i hi hiR
  exact fix_reflection_nd hdis D₁ D₂ hV2 hn g (by rw [hsup]; exact hv) hvf hi hiR.1 hiR.2

theorem vmodel_rho_eq_iff {n : ℕ} {ρ : SLt n →* MulAut V} {U : Subgroup V} {X : Type} [CommGroup X]
    {act : SLt n → X → X} (D : VModel n ρ U ⊥ X act) {u v : V} (hu : u ∈ U) (hv : v ∈ U) (y : SLt n) :
    ρ y u = v ↔ act y (D.β ⟨u, hu⟩) = D.β ⟨v, hv⟩ := by
  have h1 := D.equiv y ⟨u, hu⟩ (D.inv y u hu)
  constructor
  · intro h
    rw [← h1]
    exact congrArg D.β (Subtype.ext h)
  · intro h
    rw [← h1] at h
    exact congrArg Subtype.val (D.β_injective h)

end Vectors

section Dual

variable {V : Type} [CommGroup V]

theorem actDl_eq_iff {n : ℕ} (y : SLt n) (a b : Multiplicative (Vt n)) :
    actDl y a = b ↔ (mat y)ᵀ *ᵥ Multiplicative.toAdd b = Multiplicative.toAdd a := by
  constructor
  · intro h
    rw [← h, toAdd_actDl, mulVec_mulVec, ← transpose_mul, ← mat_mul, inv_mul_cancel, mat_one,
      transpose_one, one_mulVec]
  · intro h
    apply Multiplicative.toAdd.injective
    rw [toAdd_actDl, ← h, mulVec_mulVec, ← transpose_mul, ← mat_mul, mul_inv_cancel, mat_one,
      transpose_one, one_mulVec]

@[expose] def e4 : Multiplicative (Vt 4) := Multiplicative.ofAdd ![0, 0, 0, 1]

@[expose] def w4 : Multiplicative (Vt 4) := Multiplicative.ofAdd ![0, 1, 1, 0]

theorem actDl_e4_of_mem {t : SLt 4} (ht : t ∈ QI 4 {3}) : actDl t e4 = e4 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_actDl]
  exact dual_fix_last (by norm_num) (g := t) ht (w := ![0, 0, 0, 1]) (by decide)

theorem actDl_e4_ne_one (g : SLt 4) : actDl g e4 ≠ 1 := by
  intro h
  rw [actDl_eq_iff] at h
  have h2 : (0 : Vt 4) = ![0, 0, 0, 1] := by simpa [e4] using h
  have h3 := congrFun h2 3
  revert h3
  decide

@[expose] def t3M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 1, 0, 0; 1, 1, 1, 1; 0, 0, 0, 1]

theorem t3M_det : t3M.det = 1 := by decide

@[expose] def t3 : SLt 4 := ⟨t3M, t3M_det⟩

theorem t3_pow : t3 ^ 3 = 1 := by
  apply Subtype.ext
  show t3M ^ 3 = 1
  decide

theorem t3_mem : t3 ∈ QI 4 {3} := mem_QI_single_of (by decide +revert)

theorem actDl_t3_g3 : actDl (t3 * g3) w4 = e4 * w4 := by
  rw [actDl_eq_iff]
  show (mat (t3 * g3))ᵀ *ᵥ (![0, 0, 0, 1] + ![0, 1, 1, 0]) = ![0, 1, 1, 0]
  rw [mat_mul]
  show (t3M * g3M)ᵀ *ᵥ _ = _
  decide

private theorem conj_mul_conj_aux {G : Type*} [Group G] (g a b : G) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by
  group

theorem exists_q_dual {ρ : SLt 4 →* MulAut V} {U₂ : Subgroup V}
    (D₂ : VModel 4 ρ U₂ ⊥ (Multiplicative (Vt 4)) actDl) (g : SLt 4) {P : Subgroup (MulAut V)}
    (hP₁ : ∀ a ∈ P, ∃ t ∈ QI 4 {3}, ρ (g * t * g⁻¹) = a)
    (hP₂ : ∀ t ∈ QI 4 {3}, ρ (g * t * g⁻¹) ∈ P) :
    ∃ q ∈ U₂, q ≠ 1 ∧ (∀ a ∈ P, a q = q) ∧ q ∈ commV (oTwoUpper P) := by
  obtain ⟨q₀, hq₀⟩ := D₂.surj (actDl g e4)
  obtain ⟨x₀, hx₀⟩ := D₂.surj (actDl g w4)
  have hq₀U : (q₀ : V) ∈ U₂ := q₀.2
  have hx₀U : (x₀ : V) ∈ U₂ := x₀.2
  have hβq : D₂.β ⟨(q₀ : V), hq₀U⟩ = actDl g e4 := hq₀
  have hβx : D₂.β ⟨(x₀ : V), hx₀U⟩ = actDl g w4 := hx₀
  refine ⟨(q₀ : V), hq₀U, ?_, ?_, ?_⟩
  · intro h1
    have h2 : q₀ = 1 := Subtype.ext h1
    rw [h2, map_one] at hq₀
    exact actDl_e4_ne_one g hq₀.symm
  · intro a ha
    obtain ⟨t, ht, rfl⟩ := hP₁ a ha
    refine (vmodel_rho_eq_iff D₂ hq₀U hq₀U _).2 ?_
    rw [hβq, ← actDl_mul, inv_mul_cancel_right, actDl_mul, actDl_e4_of_mem ht]
  · have hodd : ∀ (t : SLt 4) (m : ℕ), Odd m → t ^ m = 1 → t ∈ QI 4 {3} →
        ρ (g * t * g⁻¹) ∈ oTwoUpper P := by
      intro t m hm htm ht
      refine mem_oTwoUpper_of_odd (hP₂ t ht) ?_
      have h1 : (ρ (g * t * g⁻¹)) ^ m = 1 := by
        rw [← map_pow, conj_pow, htm, mul_one, mul_inv_cancel, map_one]
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
    have ha₁ := hodd t3 3 (by decide) t3_pow t3_mem
    have ha₂ := hodd g3 7 (by decide) g3_pow g3_mem
    refine Subgroup.subset_closure ⟨_, (oTwoUpper P).mul_mem ha₁ ha₂, (x₀ : V), ?_⟩
    have hprod : ρ (g * t3 * g⁻¹) * ρ (g * g3 * g⁻¹) = ρ (g * (t3 * g3) * g⁻¹) := by
      rw [← map_mul, conj_mul_conj_aux]
    rw [hprod, mul_inv_eq_iff_eq_mul]
    have hv : (q₀ : V) * (x₀ : V) ∈ U₂ := U₂.mul_mem hq₀U hx₀U
    refine (vmodel_rho_eq_iff D₂ hx₀U hv _).2 ?_
    have hβm : D₂.β ⟨(q₀ : V) * (x₀ : V), hv⟩ = D₂.β ⟨(q₀ : V), hq₀U⟩ * D₂.β ⟨(x₀ : V), hx₀U⟩ :=
      map_mul D₂.β q₀ x₀
    rw [hβm, hβq, hβx, ← actDl_mul, inv_mul_cancel_right, actDl_mul, actDl_t3_g3, actDl_hom]

end Dual

section Fixed

variable {V : Type} [CommGroup V]

theorem fixN4 : ∀ x : Fin 4 → ZMod 2,
    (∀ a b : Fin 4, a ≠ b → (1 + Matrix.single a b (1 : ZMod 2)) *ᵥ x = x) → x = 0 := by
  decide +kernel

theorem fixD4 : ∀ x : Fin 4 → ZMod 2,
    (∀ a b : Fin 4, a ≠ b → (1 + Matrix.single a b (1 : ZMod 2))ᵀ *ᵥ x = x) → x = 0 := by
  decide +kernel

theorem eq_zero_of_fixed_nat {x : Vt 4} (h : ∀ y : SLt 4, mat y *ᵥ x = x) : x = 0 :=
  fixN4 x fun a b hab => by
    have h1 := h (SpecialLinearGroup.transvection hab (1 : ZMod 2))
    rwa [show mat (SpecialLinearGroup.transvection hab (1 : ZMod 2)) =
      1 + Matrix.single a b (1 : ZMod 2) from SpecialLinearGroup.transvection_coe hab 1] at h1

theorem eq_zero_of_fixed_dual {x : Vt 4} (h : ∀ y : SLt 4, (mat y)ᵀ *ᵥ x = x) : x = 0 :=
  fixD4 x fun a b hab => by
    have h1 := h (SpecialLinearGroup.transvection hab (1 : ZMod 2))
    rwa [show mat (SpecialLinearGroup.transvection hab (1 : ZMod 2)) =
      1 + Matrix.single a b (1 : ZMod 2) from SpecialLinearGroup.transvection_coe hab 1] at h1

theorem fixV_inf_eq_bot_nd {Λ : Subgroup (MulAut V)} {U U₁ U₂ : Subgroup V}
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥Λ} (hsup : U₁ ⊔ U₂ = U) (hdis : U₁ ⊓ U₂ = ⊥)
    (D₁ : VModel 4 (rhoOf π) U₁ ⊥ (Multiplicative (Vt 4)) (fun g a => actM g a))
    (D₂ : VModel 4 (rhoOf π) U₂ ⊥ (Multiplicative (Vt 4)) actDl) : fixV Λ ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvf, hvU⟩
  rw [← hsup] at hvU
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.1 hvU
  have hcomp : ∀ y : SLt 4, rhoOf π y v₁ = v₁ ∧ rhoOf π y v₂ = v₂ := fun y =>
    fixed_of_two hdis (rhoOf π y) (fun u hu => D₁.inv y u hu) (fun u hu => D₂.inv y u hu) hv₁ hv₂
      (hvf (rhoOf π y) (rhoOf_mem π y))
  have h1 : D₁.β ⟨v₁, hv₁⟩ = 1 := by
    have hz : Multiplicative.toAdd (D₁.β ⟨v₁, hv₁⟩) = 0 := by
      apply eq_zero_of_fixed_nat
      intro y
      exact congrArg Multiplicative.toAdd ((vmodel_rho_eq_iff D₁ hv₁ hv₁ y).1 (hcomp y).1)
    exact Multiplicative.toAdd.injective hz
  have h2 : D₂.β ⟨v₂, hv₂⟩ = 1 := by
    have hz : Multiplicative.toAdd (D₂.β ⟨v₂, hv₂⟩) = 0 := by
      apply eq_zero_of_fixed_dual
      intro y
      exact (actDl_eq_iff y _ _).1 ((vmodel_rho_eq_iff D₂ hv₂ hv₂ y).1 (hcomp y).2)
    exact Multiplicative.toAdd.injective hz
  have e1 : v₁ = 1 := Subgroup.mem_bot.1 (D₁.ker _ h1)
  have e2 : v₂ = 1 := Subgroup.mem_bot.1 (D₂.ker _ h2)
  rw [e1, e2, mul_one]
  exact Subgroup.one_mem _

end Fixed

end CFSG.Quasithin.A38c10
