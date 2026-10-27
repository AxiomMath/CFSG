module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem relIndex_sup_eq_relIndex_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

omit [Finite G] in
theorem relIndex_inf_of_le {X Y K : Subgroup G} (h : X ≤ Y) :
    (Y ⊓ K).relIndex X = K.relIndex X := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun hx => hx.2, fun hx => ⟨h x.2, hx⟩⟩

section SL2

variable {F : Type} [Field F]

theorem sl2X_mul_sl2X (b c : F) : sl2X b * sl2X c = sl2X (b + c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2X, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2X_zero : sl2X (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2X]

theorem sl2Stab_comm_sq [CharP F 2] {v : Fin 2 → F} (hv : v ≠ 0)
    {A A' : Matrix.SpecialLinearGroup (Fin 2) F} (hA : A ∈ sl2Stab v) (hA' : A' ∈ sl2Stab v) :
    A * A' = A' * A ∧ A * A = 1 := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  obtain ⟨b, rfl⟩ := (mem_sl2Stab_iff hB A).mp hA
  obtain ⟨c, rfl⟩ := (mem_sl2Stab_iff hB A').mp hA'
  constructor
  · calc B * sl2X b * B⁻¹ * (B * sl2X c * B⁻¹) = B * (sl2X b * sl2X c) * B⁻¹ := by group
      _ = B * (sl2X c * sl2X b) * B⁻¹ := by rw [sl2X_mul_sl2X, sl2X_mul_sl2X, add_comm]
      _ = B * sl2X c * B⁻¹ * (B * sl2X b * B⁻¹) := by group
  · calc B * sl2X b * B⁻¹ * (B * sl2X b * B⁻¹) = B * (sl2X b * sl2X b) * B⁻¹ := by group
      _ = 1 := by rw [sl2X_mul_sl2X, CharTwo.add_self_eq_zero, sl2X_zero]; group

end SL2

namespace Hyp611Nat

variable (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K} (hv : v ≠ 0)
  (hle : h.rhoTL ≤ sl2Stab v)
include hv hle

noncomputable def stabMat (s : ↥(ch6S T L V)) : ↥(sl2Stab v) :=
  ⟨Classical.choose (h.exists_stab_of_mem_S hv hle s.2),
    (Classical.choose_spec (h.exists_stab_of_mem_S hv hle s.2)).1⟩

theorem stabMat_spec (s : ↥(ch6S T L V)) (w : Fin 2 → h.data.K) :
    h.data.conj ⟨s, h.toHyp611.T_le_normalizer s.2.1⟩ w =
      (((h.stabMat hv hle s : ↥(sl2Stab v)) : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec w :=
  (Classical.choose_spec (h.exists_stab_of_mem_S hv hle s.2)).2 w

noncomputable def stabHom : ↥(ch6S T L V) →* ↥(sl2Stab v) where
  toFun := h.stabMat hv hle
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply matrix_eq_of_mulVec_eq
    intro w
    rw [← h.stabMat_spec hv hle 1 w, h.data.conj_eq_of_mem_centralizer _ (Subgroup.one_mem _) w]
    simp
  map_mul' := fun s t => by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    apply matrix_eq_of_mulVec_eq
    intro w
    rw [← Matrix.mulVec_mulVec, ← h.stabMat_spec hv hle, ← h.stabMat_spec hv hle,
      ← h.stabMat_spec hv hle, ← h.data.conj_mul]
    rfl

theorem stabHom_eq_one_iff (s : ↥(ch6S T L V)) :
    h.stabHom hv hle s = 1 ↔ (s : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h1
    refine h.data.mem_centralizer_of_conj_eq ⟨s, h.toHyp611.T_le_normalizer s.2.1⟩ fun w => ?_
    rw [h.stabMat_spec hv hle s w]
    have : h.stabMat hv hle s = 1 := h1
    rw [this]
    simp
  · intro hs
    apply Subtype.ext
    apply Subtype.ext
    apply matrix_eq_of_mulVec_eq
    intro w
    have e := h.stabMat_spec hv hle s w
    rw [h.data.conj_eq_of_mem_centralizer _ hs w] at e
    show (((h.stabMat hv hle s : ↥(sl2Stab v)) : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec w = _
    rw [← e]
    simp

end Hyp611Nat

namespace Hyp611Nat

theorem isElemAbelianMod_of_le_S (h : Hyp611Nat G T M L V n) {X : Subgroup G}
    (hX : X ≤ ch6S T L V) : IsElemAbelianMod X (X ⊓ Subgroup.centralizer (V : Set G)) := by
  have := charP_two_of_two_dvd h.two_dvd_card_K
  obtain ⟨v, hv, hle⟩ := h.exists_line
  intro u hu w hw
  refine ⟨⟨X.mul_mem (X.mul_mem (X.mul_mem hu hw) (X.inv_mem hu)) (X.inv_mem hw), ?_⟩,
    ⟨X.pow_mem hu 2, h.sq_mem_centralizer (hX hu)⟩⟩
  set φ := h.stabHom hv hle
  let u' : ↥(ch6S T L V) := ⟨u, hX hu⟩
  let w' : ↥(ch6S T L V) := ⟨w, hX hw⟩
  have hc := (sl2Stab_comm_sq hv (φ u').2 (φ w').2).1
  have h1 : φ (u' * w' * u'⁻¹ * w'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [hc]
    group
  have := (h.stabHom_eq_one_iff hv hle _).mp h1
  simpa [u', w'] using this

theorem relIndex_le_of_le_S (h : Hyp611Nat G T M L V n) {X : Subgroup G}
    (hX : X ≤ ch6S T L V) :
    (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X ≤ 2 ^ n := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  let ψ : ↥X →* ↥(sl2Stab v) := (h.stabHom hv hle).comp (Subgroup.inclusion hX)
  have hker : ψ.ker = (X ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply]
    rw [h.stabHom_eq_one_iff hv hle]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have h1 : (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X = Nat.card ψ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [h1, ← h.data.card, ← card_sl2Stab hv]
  exact Subgroup.card_le_card_group _

end Hyp611Nat

namespace Hyp6116

theorem conjClosure_le_S (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ ch6S T L V :=
  (h.lemma_6_1_20_one h432).1.trans (F7.isSylowTwoOf_pCoreOf_le h.toHyp611Nat.isSylowIn_S)

theorem exists_commutator_ne (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) :
    ∃ x ∈ Subgroup.centralizer (ch6ZS T L V : Set G), ⁅V, conjSub x V⁆ ≠ ⊥ := by
  by_contra hall
  push Not at hall
  apply h.lemma_6_1_20_two h432 h6111 h6119
  have hcomm : ∀ i ∈ Subgroup.centralizer (ch6ZS T L V : Set G), ∀ a ∈ V,
      ∀ j ∈ Subgroup.centralizer (ch6ZS T L V : Set G), ∀ b ∈ V,
      i * a * i⁻¹ * (j * b * j⁻¹) = j * b * j⁻¹ * (i * a * i⁻¹) := by
    intro i hi a ha j hj b hb
    have h1 := hall (i⁻¹ * j) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hi) hj)
    have h2 : ∀ c ∈ conjSub (i⁻¹ * j) V, a * c = c * a := by
      intro c hc
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 ha
      exact (Subgroup.mem_centralizer_iff.mp this c hc).symm
    have h3 := h2 _ (mul_mem_conjSub hb)
    calc i * a * i⁻¹ * (j * b * j⁻¹) = i * (a * (i⁻¹ * j * b * (i⁻¹ * j)⁻¹)) * i⁻¹ := by group
      _ = i * ((i⁻¹ * j * b * (i⁻¹ * j)⁻¹) * a) * i⁻¹ := by rw [h3]
      _ = j * b * j⁻¹ * (i * a * i⁻¹) := by group
  have hle : conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
      Subgroup.centralizer ((conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) :
        Subgroup G) : Set G) := by
    unfold conjClosure
    rw [Subgroup.centralizer_closure, Subgroup.closure_le]
    rintro x ⟨i, hi, a, ha, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro y ⟨j, hj, b, hb, rfl⟩
    exact hcomm j hj b hb i hi a ha
  exact ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle y.2) x x.2)⟩⟩

theorem le_sup_inf_centralizer (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h : Hyp6116 G T M L V n)
    {x : G} (hx : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) (hne : ⁅V, conjSub x V⁆ ≠ ⊥) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ conjSub x V ⊔
      (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        Subgroup.centralizer (V : Set G)) ∧
    (conjSub x V ⊓ Subgroup.centralizer (V : Set G)).relIndex (conjSub x V) = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have hUS := h.conjClosure_le_S h432
  have hUN : U ≤ Subgroup.normalizer (V : Set G) :=
    hUS.trans (inf_le_left.trans h.toHyp611.T_le_normalizer)
  have hWU : conjSub x V ≤ U := Hyp6116.conjSub_le_conjClosure hx
  have hWN : conjSub x V ≤ Subgroup.normalizer (V : Set G) := hWU.trans hUN
  have hWC : ¬ conjSub x V ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hne
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
  have heq : conjSubgroup V x⁻¹ = conjSub x V := by
    unfold conjSubgroup conjSub
    rw [inv_inv]
  have h3 := (h6110 G T M L V n h.toHyp611Nat).2.2 x⁻¹ (heq ▸ hWN) (heq ▸ hWC)
  rw [heq] at h3
  have hW2 : IsPGroup 2 (conjSub x V) :=
    (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).map _
  have hidx : (conjSub x V ⊓ Subgroup.centralizer (V : Set G)).relIndex (conjSub x V) = 2 ^ n := by
    rw [relIndex_eq_two_pow hW2, h3]
  refine ⟨?_, hidx⟩
  have hBN : conjSub x V ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro w hw
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hWU hw), F7.normalizer_le_normalizer_centralizer V (hWN hw)⟩
  have h1 : (U ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (conjSub x V ⊔ (U ⊓ Subgroup.centralizer (V : Set G))) = 2 ^ n := by
    rw [relIndex_sup_eq_relIndex_of_le_normalizer hBN, relIndex_inf_of_le hWU,
      ← Subgroup.inf_relIndex_left]
    exact hidx
  have h2 : (U ⊓ Subgroup.centralizer (V : Set G)).relIndex U ≤ 2 ^ n :=
    h.toHyp611Nat.relIndex_le_of_le_S hUS
  have h4 := Subgroup.relIndex_mul_relIndex (U ⊓ Subgroup.centralizer (V : Set G))
    (conjSub x V ⊔ (U ⊓ Subgroup.centralizer (V : Set G))) U le_sup_right
    (sup_le hWU inf_le_left)
  rw [h1] at h4
  have h5 : (conjSub x V ⊔ (U ⊓ Subgroup.centralizer (V : Set G))).relIndex U = 1 := by
    have h6 := relIndex_ne_zero' U (conjSub x V ⊔ (U ⊓ Subgroup.centralizer (V : Set G)))
    have h7 : 0 < 2 ^ n := by positivity
    by_contra h8
    have h9 : 2 ^ n * 2 ≤ 2 ^ n *
        (conjSub x V ⊔ (U ⊓ Subgroup.centralizer (V : Set G))).relIndex U :=
      Nat.mul_le_mul_left _ (by omega)
    generalize 2 ^ n = q at *
    omega
  exact Subgroup.relIndex_eq_one.mp h5

end Hyp6116

end CFSG.Quasithin.H13
