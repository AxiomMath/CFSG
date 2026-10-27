module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Minus4
public import CFSG.RankThree.GF2n.Stroth80.Sec7RootLemma
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped Matrix

namespace HS6

section Torus

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure TwoPairs (Q : QuadraticForm K V) (e f w₀ w₁ : V) : Prop where
  he : Q e = 0
  hf : Q f = 0
  hw₀ : Q w₀ = 0
  hw₁ : Q w₁ = 0
  ef : polar Q e f = 1
  ww : polar Q w₀ w₁ = 1
  e_w₀ : polar Q e w₀ = 0
  e_w₁ : polar Q e w₁ = 0
  f_w₀ : polar Q f w₀ = 0
  f_w₁ : polar Q f w₁ = 0

variable {e f w₀ w₁ : V}

theorem TwoPairs.X_apply (h : TwoPairs Q e f w₀ w₁) (a : K) (x : V) :
    eichler Q w₀ (a • e) x = x + (a * polar Q x w₀) • e - (a * polar Q x e) • w₀ := by
  have hw : polar Q w₀ (a • e) = 0 := by
    rw [polar_smul_right_eq, polar_comm, h.e_w₀, mul_zero]
  rw [eichler_apply h.hw₀ hw, polar_smul_right_eq, map_smul_eq_sq, h.he]
  module

theorem TwoPairs.Y_apply (h : TwoPairs Q e f w₀ w₁) (b : K) (x : V) :
    eichler Q f (b • w₁) x = x + (b * polar Q x f) • w₁ - (b * polar Q x w₁) • f := by
  have hw : polar Q f (b • w₁) = 0 := by
    rw [polar_smul_right_eq, h.f_w₁, mul_zero]
  rw [eichler_apply h.hf hw, polar_smul_right_eq, map_smul_eq_sq, h.hw₁]
  module

theorem TwoPairs.X_e (h : TwoPairs Q e f w₀ w₁) (a : K) : eichler Q w₀ (a • e) e = e := by
  rw [h.X_apply, polar_self_eq_zero h.he, h.e_w₀]
  simp

theorem TwoPairs.X_f (h : TwoPairs Q e f w₀ w₁) (a : K) :
    eichler Q w₀ (a • e) f = f - a • w₀ := by
  rw [h.X_apply, h.f_w₀, polar_comm Q f e, h.ef]
  simp

theorem TwoPairs.X_w₀ (h : TwoPairs Q e f w₀ w₁) (a : K) : eichler Q w₀ (a • e) w₀ = w₀ := by
  rw [h.X_apply, polar_self_eq_zero h.hw₀, polar_comm Q w₀ e, h.e_w₀]
  simp

theorem TwoPairs.X_w₁ (h : TwoPairs Q e f w₀ w₁) (a : K) :
    eichler Q w₀ (a • e) w₁ = w₁ + a • e := by
  rw [h.X_apply, polar_comm Q w₁ w₀, h.ww, polar_comm Q w₁ e, h.e_w₁]
  simp

theorem TwoPairs.Y_e (h : TwoPairs Q e f w₀ w₁) (b : K) :
    eichler Q f (b • w₁) e = e + b • w₁ := by
  rw [h.Y_apply, h.ef, h.e_w₁]
  simp

theorem TwoPairs.Y_f (h : TwoPairs Q e f w₀ w₁) (b : K) : eichler Q f (b • w₁) f = f := by
  rw [h.Y_apply, polar_self_eq_zero h.hf, h.f_w₁]
  simp

theorem TwoPairs.Y_w₀ (h : TwoPairs Q e f w₀ w₁) (b : K) :
    eichler Q f (b • w₁) w₀ = w₀ - b • f := by
  rw [h.Y_apply, polar_comm Q w₀ f, h.f_w₀, h.ww]
  simp

theorem TwoPairs.Y_w₁ (h : TwoPairs Q e f w₀ w₁) (b : K) : eichler Q f (b • w₁) w₁ = w₁ := by
  rw [h.Y_apply, polar_comm Q w₁ f, h.f_w₁, polar_self_eq_zero h.hw₁]
  simp

noncomputable def torusMap (Q : QuadraticForm K V) (e f w₀ w₁ : V) (b : K) : V ≃ₗ[K] V :=
  eichler Q w₀ (b • e) * eichler Q f (b⁻¹ • w₁) * eichler Q w₀ (b • e) *
    eichler Q w₀ ((1 : K) • e) * eichler Q f ((1 : K) • w₁) * eichler Q w₀ ((1 : K) • e)

theorem TwoPairs.torusMap_e [CharP K 2] (h : TwoPairs Q e f w₀ w₁) {b : K} (hb : b ≠ 0) :
    torusMap Q e f w₀ w₁ b e = b • e := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [torusMap, LinearEquiv.mul_apply, map_add, map_smul, map_sub, h.X_e, h.X_f, h.X_w₀,
    h.X_w₁, h.Y_e, h.Y_f, h.Y_w₀, h.Y_w₁]
  match_scalars
  · rw [inv_mul_cancel₀ hb]
    linear_combination (2 + b) * h2
  · rw [mul_inv_cancel₀ hb]
    linear_combination (b⁻¹ + 1) * h2

theorem TwoPairs.torusMap_w₀ [CharP K 2] (h : TwoPairs Q e f w₀ w₁) {b : K} (hb : b ≠ 0) :
    torusMap Q e f w₀ w₁ b w₀ = b • w₀ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [torusMap, LinearEquiv.mul_apply, map_add, map_smul, map_sub, h.X_e, h.X_f, h.X_w₀,
    h.X_w₁, h.Y_e, h.Y_f, h.Y_w₀, h.Y_w₁]
  match_scalars
  · linear_combination (b + 2) * (inv_mul_cancel₀ hb) + (2 + b) * h2
  · linear_combination (-1 : K) * (mul_inv_cancel₀ hb) + (-(b⁻¹ + 1)) * h2

theorem torusMap_mem (Q : QuadraticForm K V) (e f w₀ w₁ : V) (b : K) :
    torusMap Q e f w₀ w₁ b ∈ elementaryGroup Q := by
  unfold torusMap
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ ?_ ?_) ?_) ?_) ?_) ?_ <;> exact eichler_mem_elementaryGroup Q _ _

end Torus

section Lom

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X')

@[expose] noncomputable def lomMat (u w : ι → K) : GL ι K :=
  ((E.equiv.symm (eichlerG Q' u w) : ↥X') : GL ι K)

theorem lomMat_mem (u w : ι → K) : lomMat E u w ∈ X' := (E.equiv.symm (eichlerG Q' u w)).2

theorem lomMat_mulVec (u w x : ι → K) :
    ((lomMat E u w : GL ι K) : Matrix ι ι K) *ᵥ x = eichler Q' u w x := by
  have h := E.app (E.equiv.symm (eichlerG Q' u w)) x
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem lomMat_mul {u v w : ι → K} (hv : polar Q' u v = 0) (hw : polar Q' u w = 0) :
    lomMat E u v * lomMat E u w = lomMat E u (v + w) := by
  unfold lomMat
  rw [← Subgroup.coe_mul, ← map_mul, eichlerG_mul hv hw]

theorem lomMat_mem_LomGL {u w : ι → K} (hw : polar Q' u w = 0) :
    lomMat E u w ∈ E.LomGL u := by
  unfold ElemMatrixIso.LomGL
  refine CFSG.ClassicalGroups.F2Fixed.mem_matrixOf_iff.mpr ⟨lomMat_mem E u w, ?_⟩
  have h : E.equiv ⟨lomMat E u w, lomMat_mem E u w⟩ = eichlerG Q' u w :=
    E.equiv.apply_symm_apply _
  rw [h]
  exact eichlerG_mem_Lom hw

theorem lomMat_conj {g : GL ι K} (hg : g ∈ X') (u w : ι → K) :
    g * lomMat E u w * g⁻¹ =
      lomMat E ((g : Matrix ι ι K) *ᵥ u) ((g : Matrix ι ι K) *ᵥ w) := by
  have h1 := eichlerG_conj (E.equiv ⟨g, hg⟩) u w
  have h2 : ∀ v, (E.equiv ⟨g, hg⟩).app v = (g : Matrix ι ι K) *ᵥ v := fun v => E.app ⟨g, hg⟩ v
  rw [h2, h2] at h1
  have h3 : (⟨g, hg⟩ : ↥X') * E.equiv.symm (eichlerG Q' u w) * (⟨g, hg⟩ : ↥X')⁻¹ =
      E.equiv.symm (eichlerG Q' ((g : Matrix ι ι K) *ᵥ u) ((g : Matrix ι ι K) *ᵥ w)) := by
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  exact congrArg (fun x : ↥X' => (x : GL ι K)) h3

variable (P : HypPair Q')

theorem proj_of_mem_perp {x : ι → K} (hx : x ∈ P.perp) : P.proj x = x := by
  have h := HypPair.mem_perp.mp hx
  rw [HypPair.proj, polar_comm Q' x P.f, h.2, polar_comm Q' x P.e, h.1]
  simp

theorem proj_smul (a : K) (x : ι → K) : P.proj (a • x) = a • P.proj x := by
  unfold HypPair.proj
  rw [polar_smul_left_eq, polar_smul_left_eq]
  module

@[expose] noncomputable def lomHom : Multiplicative ↥P.perp →* GL ι K :=
  MonoidHom.mk' (fun w => lomMat E P.e ((Multiplicative.toAdd w : ↥P.perp) : ι → K))
    (fun a b => by
      have ha := (HypPair.mem_perp.mp (Multiplicative.toAdd a).2).1
      have hb := (HypPair.mem_perp.mp (Multiplicative.toAdd b).2).1
      rw [toAdd_mul, Submodule.coe_add]
      exact (lomMat_mul E ha hb).symm)

theorem lomHom_apply (w : ↥P.perp) :
    lomHom E P (Multiplicative.ofAdd w) = lomMat E P.e (w : ι → K) := rfl

theorem lomHom_injective (hQ : (polarBilin Q').Nondegenerate) :
    Function.Injective (lomHom E P) := by
  intro a b hab
  have ha := HypPair.mem_perp.mp (Multiplicative.toAdd a).2
  have hb := HypPair.mem_perp.mp (Multiplicative.toAdd b).2
  have h1 : eichler Q' P.e ((Multiplicative.toAdd a : ↥P.perp) : ι → K) =
      eichler Q' P.e ((Multiplicative.toAdd b : ↥P.perp) : ι → K) := by
    refine LinearEquiv.ext fun x => ?_
    rw [← lomMat_mulVec E, ← lomMat_mulVec E]
    exact congrArg (fun A : GL ι K => (A : Matrix ι ι K) *ᵥ x) hab
  obtain ⟨c, hc⟩ := (eichler_eq_eichler_iff hQ P.Q_e P.e_ne_zero ha.1 hb.1).mp h1
  have hc0 : c = 0 := by
    have h := hb.2
    rw [hc, polar_add_right, polar_smul_right_eq, ha.2, P.polar_fe, mul_one, zero_add] at h
    exact h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [hc, hc0, zero_smul, add_zero]

theorem lomHom_range (hQ : (polarBilin Q').Nondegenerate) :
    (lomHom E P).range = E.LomGL P.e := by
  ext A
  constructor
  · rintro ⟨w, rfl⟩
    exact lomMat_mem_LomGL E (HypPair.mem_perp.mp (Multiplicative.toAdd w).2).1
  · intro hA
    obtain ⟨w, hw, hwA⟩ := eichler_of_mem_LomGL E hA
    have h := P.eq_add_proj w
    have hw' : polar Q' w P.e = 0 := by rw [polar_comm]; exact hw
    rw [hw', zero_smul, add_zero] at h
    have hEw : eichler Q' P.e w = eichler Q' P.e (P.proj w) :=
      calc eichler Q' P.e w = eichler Q' P.e (P.proj w + polar Q' w P.f • P.e) :=
            congrArg _ (by rw [add_comm]; exact h)
        _ = eichler Q' P.e (P.proj w) := eichler_add_smul_self P.Q_e _ _
    refine ⟨Multiplicative.ofAdd ⟨P.proj w, P.proj_mem_perp w⟩, ?_⟩
    apply Units.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    show ((lomMat E P.e (P.proj w) : GL ι K) : Matrix ι ι K) *ᵥ x = (A : Matrix ι ι K) *ᵥ x
    rw [lomMat_mulVec, hwA x, hEw]

theorem lomMat_conj_perp {g : GL ι K} (hg : g ∈ X') {d : K} (hd : d ≠ 0)
    (hge : (g : Matrix ι ι K) *ᵥ P.e = d • P.e) {w : ι → K} (hw : w ∈ P.perp) :
    g * lomMat E P.e w * g⁻¹ =
      lomMat E P.e (P.proj (d • ((g : Matrix ι ι K) *ᵥ w))) := by
  rw [lomMat_conj E hg, hge]
  have hperp : polar Q' P.e (d • ((g : Matrix ι ι K) *ᵥ w)) = 0 := by
    rw [polar_smul_right_eq]
    have h2 : d⁻¹ • ((g : Matrix ι ι K) *ᵥ P.e) = P.e := by
      rw [hge, smul_smul, inv_mul_cancel₀ hd, one_smul]
    have h3 : polar Q' P.e ((g : Matrix ι ι K) *ᵥ w) = 0 := by
      calc polar Q' P.e ((g : Matrix ι ι K) *ᵥ w)
          = polar Q' (d⁻¹ • ((g : Matrix ι ι K) *ᵥ P.e)) ((g : Matrix ι ι K) *ᵥ w) := by
            rw [h2]
        _ = d⁻¹ * polar Q' P.e w := by
            rw [polar_smul_left_eq, E.polar_mulVec hg]
        _ = 0 := by rw [(HypPair.mem_perp.mp hw).1, mul_zero]
    rw [h3, mul_zero]
  have hy : d • ((g : Matrix ι ι K) *ᵥ w) =
      P.proj (d • ((g : Matrix ι ι K) *ᵥ w)) +
        polar Q' (d • ((g : Matrix ι ι K) *ᵥ w)) P.f • P.e := by
    have h := P.eq_add_proj (d • ((g : Matrix ι ι K) *ᵥ w))
    rw [polar_comm Q' (d • ((g : Matrix ι ι K) *ᵥ w)) P.e, hperp, zero_smul, add_zero] at h
    rw [add_comm]
    exact h
  have h1 : lomMat E (d • P.e) ((g : Matrix ι ι K) *ᵥ w) =
      lomMat E P.e (d • ((g : Matrix ι ι K) *ᵥ w)) := by
    unfold lomMat
    rw [eichlerG_smul_left]
  rw [h1]
  unfold lomMat
  congr 2
  conv_lhs => rw [hy]
  exact eichlerG_add_smul_self P.Q_e _ _

end Lom

section Moves

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X')
  (P : HypPair Q')

include E

theorem exists_g_trans (hmin : IsMinus (Q'.restrict P.perp) 2) {w w' : ↥P.perp}
    (hw : Q'.restrict P.perp w = 0) (hw0 : w ≠ 0) (hw' : Q'.restrict P.perp w' = 0)
    (hw0' : w' ≠ 0) :
    ∃ g ∈ X', (g : Matrix ι ι K) *ᵥ P.e = P.e ∧ ∃ c : K, c ≠ 0 ∧
      P.proj ((g : Matrix ι ι K) *ᵥ (w : ι → K)) = c • (w' : ι → K) := by
  by_cases hl : lineGrp K w = lineGrp K w'
  · obtain ⟨c, hc, hcw⟩ := (lineGrp_eq_iff hw0 hw0').mp hl
    refine ⟨1, X'.one_mem, by simp, c⁻¹, inv_ne_zero hc, ?_⟩
    have h1 : ((1 : GL ι K) : Matrix ι ι K) *ᵥ (w : ι → K) = (w : ι → K) := by
      simp
    rw [h1, proj_of_mem_perp P w.2, hcw, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
  ·
    haveI : Finite ↥P.perp := Module.finite_of_finite K
    have hcard := ncard_singLines (K := K) hmin
    have hlt : ({lineGrp K w, lineGrp K w'} : Set (Subgroup (Multiplicative ↥P.perp))).ncard <
        (singLines K (Q'.restrict P.perp)).ncard := by
      rw [hcard]
      have h1 := Set.ncard_insert_le (lineGrp K w) {lineGrp K w'}
      rw [Set.ncard_singleton] at h1
      have h2 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have h3 : 2 ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    obtain ⟨ℓ, hℓ, hℓn⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    obtain ⟨y, hQy, hy0, rfl⟩ := hℓ
    have hyw : lineGrp K y ≠ lineGrp K w := fun h => hℓn (Or.inl h)
    have hyw' : lineGrp K y ≠ lineGrp K w' := fun h => hℓn (Or.inr h)
    have hind : ∀ {z : ↥P.perp}, z ≠ 0 → lineGrp K y ≠ lineGrp K z → ∀ c : K, z ≠ c • y := by
      intro z hz hne c hc
      apply hne
      refine (lineGrp_eq_iff hy0 hz).mpr ⟨c, ?_, hc⟩
      rintro rfl
      rw [zero_smul] at hc
      exact hz hc
    have ht₁ : polar (Q'.restrict P.perp) y w ≠ 0 :=
      polar_ne_zero_of_isMinus hmin hQy hw hy0 (hind hw0 hyw)
    have ht₂ : polar (Q'.restrict P.perp) y w' ≠ 0 :=
      polar_ne_zero_of_isMinus hmin hQy hw' hy0 (hind hw0' hyw')
    rw [polar_restrict] at ht₁ ht₂
    set t₁ := polar Q' (y : ι → K) (w : ι → K) with ht₁def
    set t₂ := polar Q' (y : ι → K) (w' : ι → K) with ht₂def
    set l : K := t₁ / t₂ with hl'
    have hl0 : l ≠ 0 := div_ne_zero ht₁ ht₂
    have hQy' : Q' (y : ι → K) = 0 := hQy
    have hyl : polar Q' (y : ι → K) (l • (w' : ι → K)) = t₁ := by
      rw [polar_smul_right_eq, hl', div_mul_cancel₀ _ ht₂]
    have hQ0 : Q' (w : ι → K) = Q' (l • (w' : ι → K)) := by
      rw [map_smul_eq_sq]
      have h1 : Q' (w : ι → K) = 0 := hw
      have h2 : Q' (w' : ι → K) = 0 := hw'
      rw [h1, h2, mul_zero]
    have hperp : ∀ z : ι → K, z ∈ P.perp → polar Q' P.e z = 0 := fun z hz =>
      (HypPair.mem_perp.mp hz).1
    set v : ι → K := t₁⁻¹ • (l • (w' : ι → K) - (w : ι → K)) with hv
    have hvperp : v ∈ P.perp := P.perp.smul_mem _ (P.perp.sub_mem (P.perp.smul_mem _ w'.2) w.2)
    have hyv : polar Q' (y : ι → K) v = 0 := by
      rw [hv, polar_smul_right_eq, polar_sub_right, hyl]
      simp [← ht₁def]
    refine ⟨lomMat E (y : ι → K) v, lomMat_mem E _ _, ?_, l, hl0, ?_⟩
    · rw [lomMat_mulVec]
      exact eichler_apply_of_polar_eq_zero (hperp _ y.2) (hperp _ hvperp)
    · rw [lomMat_mulVec]
      have := eichler_apply_eq_of_polar_eq hQy' hQ0 (t := t₁) (x := (w : ι → K))
        (y := l • (w' : ι → K)) rfl hyl ht₁
      rw [show eichler Q' (y : ι → K) v (w : ι → K) = l • (w' : ι → K) from this]
      exact proj_of_mem_perp P (P.perp.smul_mem _ w'.2)

theorem exists_g_torus (hmin : IsMinus (Q'.restrict P.perp) 2) {w : ↥P.perp}
    (hw : Q'.restrict P.perp w = 0) (hw0 : w ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ g ∈ X', ∃ d : K, d ≠ 0 ∧ (g : Matrix ι ι K) *ᵥ P.e = d • P.e ∧
      P.proj (d • ((g : Matrix ι ι K) *ᵥ (w : ι → K))) = c • (w : ι → K) := by
  obtain ⟨P', hP'⟩ := exists_hypPair hmin.nondeg hw hw0
  have hpf : ∀ z : ι → K, z ∈ P.perp → polar Q' P.e z = 0 ∧ polar Q' P.f z = 0 := fun z hz =>
    HypPair.mem_perp.mp hz
  have h2 : TwoPairs Q' P.e P.f (w : ι → K) (P'.f : ι → K) :=
    { he := P.Q_e
      hf := P.Q_f
      hw₀ := hw
      hw₁ := P'.Q_f
      ef := P.polar_ef
      ww := by
        have := P'.polar_ef
        rw [hP', polar_restrict] at this
        exact this
      e_w₀ := (hpf _ w.2).1
      e_w₁ := (hpf _ P'.f.2).1
      f_w₀ := (hpf _ w.2).2
      f_w₁ := (hpf _ P'.f.2).2 }
  obtain ⟨b, hb⟩ := isSquare_of_charTwo' c
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hc (by rw [hb, mul_zero])
  let T : Gom Q' := ⟨torusMap Q' P.e P.f (w : ι → K) (P'.f : ι → K) b,
    torusMap_mem Q' _ _ _ _ _⟩
  have hT : ∀ x, ((E.equiv.symm T : ↥X') : GL ι K).val *ᵥ x =
      torusMap Q' P.e P.f (w : ι → K) (P'.f : ι → K) b x := by
    intro x
    have h := E.app (E.equiv.symm T) x
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨((E.equiv.symm T : ↥X') : GL ι K), (E.equiv.symm T).2, b, hb0, ?_, ?_⟩
  · rw [hT]
    exact h2.torusMap_e hb0
  · rw [hT, h2.torusMap_w₀ hb0, smul_smul, ← hb]
    exact proj_of_mem_perp P (P.perp.smul_mem _ w.2)

end Moves

end HS6

end CFSG.RankThree.GF2n.Stroth80
