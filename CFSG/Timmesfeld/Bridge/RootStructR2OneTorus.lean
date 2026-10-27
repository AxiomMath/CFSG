module

public import CFSG.Timmesfeld.Bridge.RootStructR2OneBasic
public import CFSG.Timmesfeld.Bridge.RootStructWTIModStep
public import CFSG.Timmesfeld.Bridge.RootStructWTIFrattini

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped Matrix

namespace RootOne

variable {G : Type} [Group G] {D : Set G}

namespace LineConf

theorem symm {a d x y : G} (C : LineConf D a d x y) : LineConf D d a y x where
  setting := C.setting
  ha := C.hd
  hd := C.ha
  had := C.had.symm
  hadD := C.hdaD
  hdT := C.haT
  hx := C.hy
  hax := C.hdy
  haxD := C.hdyD
  hxT := by rw [sup_comm]; exact C.hyT
  hy := C.hx
  hdy := C.hax
  hdyD := C.haxD
  hyT := by rw [sup_comm]; exact C.hxT

theorem x_mem_X {a d x y : G} (C : LineConf D a d x y) : x ∈ rootGroup D x ⊔ rootGroup D y :=
  Subgroup.mem_sup_left (rootSet_subset_rootGroup D x (mem_rootSet_self C.hx))

theorem y_mem_X {a d x y : G} (C : LineConf D a d x y) : y ∈ rootGroup D x ⊔ rootGroup D y :=
  Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self C.hy))

end LineConf

structure ModConf {a d x y : G} (C : LineConf D a d x y) {K : Type*} [Field K]
    (φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (θ₀ θ₁ : (Fin 2 → K) → G) : Prop where
  card_K : Nat.card K = Nat.card (rootGroup D a)
  map_x : ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
    upperUnipotent K
  map_y : ((rootGroup D y).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
    lowerUnipotent K
  conj_N : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ n ∈ lineN D a d, g * n * g⁻¹ ∈ lineN D a d
  conj_N₀ : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ n ∈ lineN₀ D a d,
    g * n * g⁻¹ ∈ lineN₀ D a d
  normal : ∀ n ∈ lineN D a d, ∀ m ∈ lineN₀ D a d, n * m * n⁻¹ ∈ lineN₀ D a d
  comm : ∀ n ∈ lineN D a d, ∀ n' ∈ lineN D a d, n * n' * n⁻¹ * n'⁻¹ ∈ lineN₀ D a d
  nat₀ : ARS.IsNaturalModule φ θ₀
  range₀ : ∀ t, t ∈ rootGroup D a ⊔ rootGroup D d ↔ ∃ v, θ₀ v = t
  axis_a : ∀ s : K, θ₀ ![s, 0] ∈ rootGroup D a
  axis_d : ∀ s : K, θ₀ ![0, s] ∈ rootGroup D d
  nat₁ : Higman.IsNaturalQuotient φ (lineN D a d) (lineN₀ D a d) θ₁
  θ₁_a : ∀ s : K, θ₁ ![s, 0] ∈ nCore D a ⊓ Subgroup.centralizer {d}
  θ₁_d : ∀ s : K, θ₁ ![0, s] ∈ nCore D d ⊓ Subgroup.centralizer {a}
  gen : Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} =
    lineN D a d ⊔ (rootGroup D x ⊔ rootGroup D y)

namespace ModConf

variable {a d x y : G} {C : LineConf D a d x y} {K : Type*} [Field K]
  {φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K}
  {θ₀ θ₁ : (Fin 2 → K) → G} (M : ModConf C φ θ₀ θ₁)
include M

theorem θ₀_mem (v : Fin 2 → K) : θ₀ v ∈ rootGroup D a ⊔ rootGroup D d :=
  (M.range₀ _).2 ⟨v, rfl⟩

theorem eq_one_of_commute {g : G} (hg : g ∈ rootGroup D x ⊔ rootGroup D y)
    (hgT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute g t) : g = 1 := by
  have h1 : ∀ v, (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
    intro v
    apply M.nat₀.injective
    rw [M.nat₀.map_mulVec]
    show g * θ₀ v * g⁻¹ = θ₀ v
    rw [(hgT _ (M.θ₀_mem v)).eq, mul_inv_cancel_right]
  have h2 : (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) = 1 :=
    Matrix.mulVec_injective (funext fun v => by rw [h1 v, Matrix.one_mulVec])
  have h3 : φ ⟨g, hg⟩ = 1 := Subtype.ext h2
  have h4 : (⟨g, hg⟩ : ↥(rootGroup D x ⊔ rootGroup D y)) = 1 := by
    rw [← map_one φ] at h3
    exact φ.injective h3
  exact congrArg Subtype.val h4

theorem mem_rootGroup_x_of_commute {g : G} (hg : g ∈ rootGroup D x ⊔ rootGroup D y)
    (hga : ∀ t ∈ rootGroup D a, Commute g t) : g ∈ rootGroup D x := by
  set A := (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) with hA
  have h1 : A *ᵥ ![1, 0] = ![1, 0] := by
    apply M.nat₀.injective
    rw [M.nat₀.map_mulVec]
    show g * θ₀ ![1, 0] * g⁻¹ = θ₀ ![1, 0]
    rw [(hga _ (M.axis_a 1)).eq, mul_inv_cancel_right]
  have h00 : A 0 0 = 1 := by
    have := congrFun h1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h10 : A 1 0 = 0 := by
    have := congrFun h1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet : A.det = 1 := (φ ⟨g, hg⟩).2
  rw [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] at hdet
  have hup : φ ⟨g, hg⟩ = RankOne.upperElt K (A 0 1) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [RankOne.upperElt, ← hA, h00, h10, hdet]
  have hmem : φ ⟨g, hg⟩ ∈ upperUnipotent K :=
    (RankOne.mem_upperUnipotent_iff K).2 ⟨_, hup⟩
  exact (ARS.NaturalModule.coe_mem_iff M.map_x ⟨g, hg⟩).2 hmem

theorem X_le_normalizer : rootGroup D x ⊔ rootGroup D y ≤
    Subgroup.normalizer ((lineN D a d : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => M.conj_N g hg n hn, fun hn => ?_⟩
  have := M.conj_N g⁻¹ (Subgroup.inv_mem _ hg) _ hn
  rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this

theorem conj_mem_lineN {h : G}
    (hT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, h * t * h⁻¹ ∈ rootGroup D a ⊔ rootGroup D d)
    (hT' : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, h⁻¹ * t * h ∈ rootGroup D a ⊔ rootGroup D d)
    {n : G} (hn : n ∈ lineN D a d) : h * n * h⁻¹ ∈ lineN D a d := by
  have hclass := C.isClass
  have hS : ∀ g ∈ {g | g ∈ D ∧ NormalizesLine D a d g}, h * g * h⁻¹ ∈
      Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} := by
    rintro g ⟨hgD, hgT⟩
    refine Subgroup.subset_closure ⟨conj_mem_of_isClass hclass h hgD, fun u hu => ?_⟩
    have e : h * g * h⁻¹ * u * (h * g * h⁻¹)⁻¹ = h * (g * (h⁻¹ * u * h) * g⁻¹) * h⁻¹ := by group
    rw [e]
    exact hT _ (hgT _ (hT' u hu))
  have hcl : ∀ g ∈ Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g},
      h * g * h⁻¹ ∈ Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact hS g hg
    | one => simp
    | mul g g' _ _ ihg ihg' =>
      rw [show h * (g * g') * h⁻¹ = h * g * h⁻¹ * (h * g' * h⁻¹) by group]
      exact Subgroup.mul_mem _ ihg ihg'
    | inv g _ ih =>
      rw [show h * g⁻¹ * h⁻¹ = (h * g * h⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ih
  have hmem : h * n * h⁻¹ ∈ Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} := by
    refine hcl n ?_
    rw [M.gen]
    exact Subgroup.mem_sup_left hn
  rw [M.gen] at hmem
  have hmem' : h * n * h⁻¹ ∈ ((lineN D a d ⊔ (rootGroup D x ⊔ rootGroup D y) : Subgroup G) :
      Set G) := hmem
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ M.X_le_normalizer] at hmem'
  obtain ⟨n', hn', g, hg, hng⟩ := hmem'
  dsimp only at hng
  have hcT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute (h * n * h⁻¹) t := by
    intro t ht
    have h1 := C.commute_of_mem_lineN hn (hT' t ht)
    have e : h * n * h⁻¹ * t = h * (n * (h⁻¹ * t * h)) * h⁻¹ := by group
    have e' : t * (h * n * h⁻¹) = h * ((h⁻¹ * t * h) * n) * h⁻¹ := by group
    show h * n * h⁻¹ * t = t * (h * n * h⁻¹)
    rw [e, e', h1.eq]
  have hgT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute g t := by
    intro t ht
    have hg' : g = n'⁻¹ * (h * n * h⁻¹) := by rw [← hng]; group
    rw [hg']
    exact (C.commute_of_mem_lineN hn' ht).inv_left.mul_left (hcT t ht)
  rw [← hng, M.eq_one_of_commute hg hgT, mul_one]
  exact hn'

theorem exists_matrix {s : G}
    (hsX : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, s * g * s⁻¹ ∈ rootGroup D x ⊔ rootGroup D y)
    (hsT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, s * t * s⁻¹ ∈ rootGroup D a ⊔ rootGroup D d)
    (hsa : ∀ t ∈ rootGroup D a, Commute s t) :
    ∃ c β : K, β ≠ 0 ∧ ∀ v, s * θ₀ v * s⁻¹ = θ₀ (!![1, c; 0, β] *ᵥ v) := by
  classical
  have hθ := M.nat₀
  have hex : ∀ v, ∃ w, θ₀ w = s * θ₀ v * s⁻¹ := fun v => (M.range₀ _).1 (hsT _ (M.θ₀_mem v))
  choose f hf using hex
  have hfadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    apply hθ.injective
    rw [hf, hθ.map_add, hθ.map_add, hf, hf]
    group
  have hf0 : ∀ r : K, f ![r, 0] = ![r, 0] := by
    intro r
    apply hθ.injective
    rw [hf, (hsa _ (M.axis_a r)).eq, mul_inv_cancel_right]
  have hfX : ∀ (g : ↥(rootGroup D x ⊔ rootGroup D y)) v,
      f ((φ g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        (φ ⟨s * g * s⁻¹, hsX g g.2⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ f v := by
    intro g v
    apply hθ.injective
    rw [hf, hθ.map_mulVec, hθ.map_mulVec, hf]
    group
  have hupper : ∀ r : K, ∃ σ : K, ∀ v,
      f ((RankOne.upperElt K r : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        (RankOne.upperElt K σ : Matrix (Fin 2) (Fin 2) K) *ᵥ f v := by
    intro r
    have hgx : ((φ.symm (RankOne.upperElt K r) : ↥(rootGroup D x ⊔ rootGroup D y)) : G) ∈
        rootGroup D x := by
      refine (ARS.NaturalModule.coe_mem_iff M.map_x _).2 ?_
      rw [MulEquiv.apply_symm_apply]
      exact (RankOne.mem_upperUnipotent_iff K).2 ⟨r, rfl⟩
    set g := φ.symm (RankOne.upperElt K r) with hg
    have hsg : s * g * s⁻¹ ∈ rootGroup D x := by
      refine M.mem_rootGroup_x_of_commute (hsX g g.2) fun t ht => ?_
      have h1 := (Commute.conj_iff s).2
        (commute_of_mem_rootGroup_of_commute' C.ha hgx ht C.hax.symm)
      rwa [(hsa t ht).eq, mul_inv_cancel_right] at h1
    obtain ⟨σ, hσ⟩ := (RankOne.mem_upperUnipotent_iff K).1
      ((ARS.NaturalModule.coe_mem_iff M.map_x ⟨_, hsX g g.2⟩).1 hsg)
    refine ⟨σ, fun v => ?_⟩
    have h1 := hfX g v
    rwa [hσ, hg, MulEquiv.apply_symm_apply] at h1
  have hf01 : ∀ w : K, f ![0, w] = ![f ![0, w] 0, f ![0, w] 1] := fun w => Higman.eq_vec _
  have hup : ∀ r : K, ∃ σ : K, ∀ w : K, r * w = σ * f ![0, w] 1 := by
    intro r
    obtain ⟨σ, hσ⟩ := hupper r
    refine ⟨σ, fun w => ?_⟩
    have h1 := hσ ![0, w]
    rw [Higman.upperElt_mulVec, Higman.upperElt_mulVec] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at h1
    rw [Higman.vec_eq_add, hfadd, hf0] at h1
    have h2 := congrFun h1 0
    simp only [Pi.add_apply, Matrix.cons_val_zero] at h2
    linear_combination h2
  set β := f ![0, 1] 1 with hβ
  set c := f ![0, 1] 0 with hc
  have hβ0 : β ≠ 0 := by
    obtain ⟨σ, hσ⟩ := hup 1
    intro h0
    have := hσ 1
    rw [← hβ, h0, mul_zero, one_mul] at this
    exact one_ne_zero this
  have hδ : ∀ w : K, f ![0, w] 1 = β * w := by
    obtain ⟨σ, hσ⟩ := hup β
    have hσ1 : σ = 1 := by
      have := hσ 1
      rw [← hβ, mul_one] at this
      have := mul_right_cancel₀ hβ0 (this.symm.trans (one_mul β).symm)
      exact this
    intro w
    rw [hσ w, hσ1, one_mul]
  set g := φ.symm (RankOne.lowerElt K 1) with hg
  set A := (φ ⟨s * g * s⁻¹, hsX g g.2⟩ : Matrix (Fin 2) (Fin 2) K) with hA
  have hlow : ∀ v, f ((RankOne.lowerElt K 1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = A *ᵥ f v := by
    intro v
    have h1 := hfX g v
    rwa [hg, MulEquiv.apply_symm_apply] at h1
  have hA10 : A 1 0 = β := by
    have h1 := hlow ![1, 0]
    rw [Higman.lowerElt_mulVec, hf0] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, add_zero] at h1
    rw [Higman.vec_eq_add, hfadd, hf0] at h1
    have h2 := congrFun h1 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
    rw [← h2]
  have hγ : ∀ w : K, f ![0, w] 0 = c * w := by
    have key : ∀ w : K, f ![0, w] 0 = (1 - A 1 1) * w := by
      intro w
      have h1 := hlow ![0, w]
      rw [Higman.lowerElt_mulVec] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add] at h1
      have h2 := congrFun h1 1
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
      rw [hδ, hA10] at h2
      have h3 : β * (f ![0, w] 0 - (1 - A 1 1) * w) = 0 := by linear_combination -h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hβ0
      · linear_combination h
    intro w
    rw [key w, hc, key 1, mul_one]
  refine ⟨c, β, hβ0, fun v => ?_⟩
  rw [← hf]
  congr 1
  rw [Higman.eq_vec v, Higman.vec_eq_add, hfadd, hf0, hf01, hγ, hδ]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit M in
theorem eq_one_of_sq_eq_one [CharP K 2] {μ : K} (h : μ ^ 2 = 1) : μ = 1 := by
  have h1 : (μ + 1) ^ 2 = 0 := by rw [CharTwo.add_sq, h, one_pow, CharTwo.add_self_eq_zero]
  have h2 : μ + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h1
  rw [← CharTwo.neg_eq (1 : K)]
  exact eq_neg_of_add_eq_zero_left h2

theorem eq_one_of_scalar [CharP K 2] {g : G} (hg : g ∈ rootGroup D x ⊔ rootGroup D y) {μ : K}
    (hμ : ∀ v, g * θ₀ v * g⁻¹ = θ₀ (μ • v)) : g = 1 := by
  have h1 : ∀ v, (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ v = (μ • 1 : Matrix _ _ K) *ᵥ v := by
    intro v
    apply M.nat₀.injective
    rw [M.nat₀.map_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact hμ v
  have h2 : (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) = μ • 1 := Matrix.mulVec_injective (funext h1)
  have hdet : (μ • (1 : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [← h2]
    exact (φ ⟨g, hg⟩).2
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hμ1 := eq_one_of_sq_eq_one hdet
  rw [hμ1, one_smul] at h2
  have h3 : φ ⟨g, hg⟩ = 1 := Subtype.ext h2
  have h4 : (⟨g, hg⟩ : ↥(rootGroup D x ⊔ rootGroup D y)) = 1 := by
    rw [← map_one φ] at h3
    exact φ.injective h3
  exact congrArg Subtype.val h4

theorem exists_scalar [CharP K 2] [PerfectRing K 2] {s : G}
    (hsX : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, s * g * s⁻¹ ∈ rootGroup D x ⊔ rootGroup D y)
    (hsT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, s * t * s⁻¹ ∈ rootGroup D a ⊔ rootGroup D d)
    (hsa : ∀ t ∈ rootGroup D a, Commute s t) (hodd : Odd (orderOf s)) :
    ∃ h₁ : G, orderOf h₁ = orderOf s ∧ (∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute h₁ g) ∧
      ∃ μ : K, μ ≠ 0 ∧ ∀ v, h₁ * θ₀ v * h₁⁻¹ = θ₀ (μ • v) := by
  have := C.finite
  obtain ⟨c, β, hβ0, hS⟩ := M.exists_matrix hsX hsT hsa
  obtain ⟨γ, hγ⟩ : ∃ γ : K, γ ^ 2 = β⁻¹ := by
    obtain ⟨γ, hγ⟩ := surjective_frobenius K 2 β⁻¹
    exact ⟨γ, by rw [← hγ, frobenius_def]⟩
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hγ
    exact hβ0 (inv_eq_zero.1 hγ.symm)
  set S : Matrix (Fin 2) (Fin 2) K := !![1, c; 0, β] with hSdef
  have hdet : (γ • S).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hSdef, Matrix.det_fin_two_of, hγ]
    field_simp
    ring
  set S' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨γ • S, hdet⟩ with hS'
  set t := φ.symm S' with ht
  have hconj : ∀ g (hg : g ∈ rootGroup D x ⊔ rootGroup D y),
      s * g * s⁻¹ = (t : G) * g * (t : G)⁻¹ := by
    intro g hg
    have hmat : (φ ⟨s * g * s⁻¹, hsX g hg⟩ : Matrix (Fin 2) (Fin 2) K) * S =
        S * (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) := by
      apply Matrix.mulVec_injective
      funext v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      apply M.nat₀.injective
      rw [M.nat₀.map_mulVec, ← hS, ← hS, M.nat₀.map_mulVec]
      group
    have h1 : φ ⟨s * g * s⁻¹, hsX g hg⟩ * S' = S' * φ ⟨g, hg⟩ := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hS']
      change (φ ⟨s * g * s⁻¹, hsX g hg⟩ : Matrix (Fin 2) (Fin 2) K) * (γ • S) =
        (γ • S) * (φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K)
      rw [Matrix.mul_smul, Matrix.smul_mul, hmat]
    have h2 : φ ⟨s * g * s⁻¹, hsX g hg⟩ = φ (t * ⟨g, hg⟩ * t⁻¹) := by
      rw [map_mul, map_mul, map_inv, ht, MulEquiv.apply_symm_apply,
        eq_mul_inv_iff_mul_eq, h1]
    have h3 := congrArg Subtype.val (φ.injective h2)
    simpa using h3
  set h₁ := (t : G)⁻¹ * s with hh₁
  have htX : (t : G) ∈ rootGroup D x ⊔ rootGroup D y := t.2
  have hts : Commute (t : G) s := by
    have := hconj t htX
    rw [mul_inv_cancel_right] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  have hcomm : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute h₁ g := by
    intro g hg
    show (t : G)⁻¹ * s * g = g * ((t : G)⁻¹ * s)
    have e := hconj g hg
    calc (t : G)⁻¹ * s * g = (t : G)⁻¹ * (s * g * s⁻¹) * s := by group
      _ = (t : G)⁻¹ * ((t : G) * g * (t : G)⁻¹) * s := by rw [e]
      _ = g * ((t : G)⁻¹ * s) := by group
  have hSinv : ((S'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * S =
      γ⁻¹ • 1 := by
    have h1 : ((S'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (γ • S) = 1 := by
      rw [show γ • S = ((S' : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        from rfl, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.mul_smul] at h1
    calc ((S'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * S =
        γ⁻¹ • (γ • (((S'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          S)) := by rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]
      _ = γ⁻¹ • 1 := by rw [h1]
  have hscal : ∀ v, h₁ * θ₀ v * h₁⁻¹ = θ₀ (γ⁻¹ • v) := by
    intro v
    have hφt : φ t = S' := by rw [ht, MulEquiv.apply_symm_apply]
    have h1 := M.nat₀.map_mulVec t⁻¹ (S *ᵥ v)
    rw [map_inv, hφt, Matrix.mulVec_mulVec, hSinv, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h1
    rw [h1, ← hS]
    simp only [Subgroup.coe_inv, hh₁]
    group
  have hpow : ∀ (n : ℕ) v, h₁ ^ n * θ₀ v * (h₁ ^ n)⁻¹ = θ₀ ((γ⁻¹) ^ n • v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, mul_inv_rev, show h₁ ^ n * h₁ * θ₀ v * (h₁⁻¹ * (h₁ ^ n)⁻¹) =
        h₁ ^ n * (h₁ * θ₀ v * h₁⁻¹) * (h₁ ^ n)⁻¹ by group, hscal, ih, smul_smul, pow_succ]
  refine ⟨h₁, ?_, hcomm, γ⁻¹, inv_ne_zero hγ0, hscal⟩
  rw [orderOf_eq_orderOf_iff]
  intro n
  have hpow' : h₁ ^ n = ((t : G) ^ n)⁻¹ * s ^ n := by
    rw [hh₁, (hts.inv_left).mul_pow, inv_pow]
  constructor
  · intro h1
    have hsn : s ^ n = (t : G) ^ n := by
      rw [h1] at hpow'
      exact (eq_of_inv_mul_eq_one hpow'.symm).symm
    have hsX' : s ^ n ∈ rootGroup D x := by
      refine M.mem_rootGroup_x_of_commute ?_ fun r hr => (hsa r hr).pow_left n
      rw [hsn]
      exact Subgroup.pow_mem _ htX n
    have h2 : IsPGroup 2 (rootGroup D x) :=
      OddLocal.isPGroup_two_of_mul_self fun _ hg => mul_self_eq_one_of_mem_rootGroup C.root C.hx hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2) ⟨_, hsX'⟩
    rw [Subgroup.orderOf_mk] at hk
    have hodd' : Odd (orderOf (s ^ n)) := hodd.of_dvd_nat (orderOf_pow_dvd n)
    rw [hk] at hodd'
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exact absurd hodd' (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, by omega⟩))
  · intro h1
    rw [h1, mul_one] at hpow'
    have hmem : h₁ ^ n ∈ rootGroup D x ⊔ rootGroup D y := by
      rw [hpow']
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ htX n)
    exact M.eq_one_of_scalar hmem (hpow n)

theorem exists_scalar_torus [CharP K 2] [PerfectRing K 2] {h₀ : G} (hodd : Odd (orderOf h₀))
    (h₀a : ∀ t ∈ rootGroup D a, Commute h₀ t)
    (h₀T : (rootGroup D a ⊔ rootGroup D d).map (MulAut.conj h₀).toMonoidHom =
      rootGroup D a ⊔ rootGroup D d) :
    ∃ h₁ : G, orderOf h₁ = orderOf h₀ ∧ (∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute h₁ g) ∧
      ∃ μ : K, μ ≠ 0 ∧ ∀ v, h₁ * θ₀ v * h₁⁻¹ = θ₀ (μ • v) := by
  have := C.finite
  set NT := Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) with hNT
  have hNT1 : ∀ z ∈ NT, ∀ t ∈ rootGroup D a ⊔ rootGroup D d,
      z * t * z⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := fun z hz t ht =>
    (Subgroup.mem_normalizer_iff.1 hz t).1 ht
  have hNT2 : ∀ z ∈ NT, ∀ t ∈ rootGroup D a ⊔ rootGroup D d,
      z⁻¹ * t * z ∈ rootGroup D a ⊔ rootGroup D d := fun z hz t ht => by
    have := hNT1 z⁻¹ (Subgroup.inv_mem _ hz) t ht
    rwa [inv_inv] at this
  have hNTN : ∀ z ∈ NT, ∀ n ∈ lineN D a d, z * n * z⁻¹ ∈ lineN D a d := fun z hz n hn =>
    M.conj_mem_lineN (hNT1 z hz) (hNT2 z hz) hn
  have hh₀NT : h₀ ∈ NT := RootSubgroup.mem_normalizer_of_map_eq h₀T
  have hNNT : ∀ n ∈ lineN D a d, n ∈ NT := fun n hn => by
    refine RootSubgroup.mem_normalizer_of_map_eq
      (map_conj_eq_of_forall_commute fun t ht => C.commute_of_mem_lineN hn ht)
  have hA : (rootGroup D a).map (MulAut.conj h₀).toMonoidHom = rootGroup D a :=
    map_conj_eq_of_forall_commute h₀a
  obtain ⟨n, hn, hnX⟩ := rootLinesFrattiniStep G D C.setting a C.ha d C.hd C.had C.hadD C.hdT x
    C.hx C.hax C.haxD C.hxT y C.hy C.hdy C.hdyD C.hyT h₀ hA h₀T
  set g := n * h₀ with hg
  have hgNT : g ∈ NT := Subgroup.mul_mem _ (hNNT n hn) hh₀NT
  have hgX : ∀ u ∈ rootGroup D x ⊔ rootGroup D y, g * u * g⁻¹ ∈ rootGroup D x ⊔ rootGroup D y :=
    fun u hu => by rw [← hnX]; exact ⟨u, hu, rfl⟩
  have hga : ∀ t ∈ rootGroup D a, Commute g t := fun t ht =>
    (C.commute_of_mem_lineN hn (Subgroup.mem_sup_left ht)).mul_left (h₀a t ht)
  have hgk : ∀ k : ℕ, ∃ n' ∈ lineN D a d, g ^ k = n' * h₀ ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨n', hn', hk⟩ := ih
      refine ⟨n' * (h₀ ^ k * n * (h₀ ^ k)⁻¹), Subgroup.mul_mem _ hn'
        (hNTN _ (Subgroup.pow_mem _ hh₀NT k) n hn), ?_⟩
      rw [pow_succ, hk, hg]
      group
  have hN2 : IsPGroup 2 (lineN D a d) := C.isPGroup_lineN
  obtain ⟨n₁, hn₁, hgo⟩ := hgk (orderOf h₀)
  rw [pow_orderOf_eq_one, mul_one] at hgo
  obtain ⟨r, hr⟩ := (IsPGroup.iff_orderOf.1 hN2) ⟨n₁, hn₁⟩
  rw [Subgroup.orderOf_mk, ← hgo] at hr
  set s := g ^ (2 ^ r) with hs
  have hsNT : s ∈ NT := Subgroup.pow_mem _ hgNT _
  have hgkX : ∀ (k : ℕ), ∀ u ∈ rootGroup D x ⊔ rootGroup D y,
      g ^ k * u * (g ^ k)⁻¹ ∈ rootGroup D x ⊔ rootGroup D y := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [show g ^ (k + 1) * u * (g ^ (k + 1))⁻¹ = g ^ k * (g * u * g⁻¹) * (g ^ k)⁻¹ by group]
      exact ih _ (hgX u hu)
  have hsX : ∀ u ∈ rootGroup D x ⊔ rootGroup D y, s * u * s⁻¹ ∈ rootGroup D x ⊔ rootGroup D y :=
    hgkX _
  have hsa : ∀ t ∈ rootGroup D a, Commute s t := fun t ht => (hga t ht).pow_left _
  have hcop : Nat.Coprime (2 ^ r) (orderOf h₀) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  have hso : orderOf s = orderOf h₀ := by
    rw [orderOf_eq_orderOf_iff]
    intro k
    constructor
    · intro hsk
      obtain ⟨n', hn', hk⟩ := hgk (2 ^ r * k)
      rw [pow_mul, ← hs, hsk, eq_comm, mul_eq_one_iff_eq_inv] at hk
      have hmem : h₀ ^ (2 ^ r * k) ∈ lineN D a d := by
        have := Subgroup.inv_mem _ hn'
        rwa [hk, inv_inv] at this
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hN2) ⟨_, hmem⟩
      rw [Subgroup.orderOf_mk] at hj
      have hodd' : Odd (orderOf (h₀ ^ (2 ^ r * k))) := hodd.of_dvd_nat (orderOf_pow_dvd _)
      rw [hj] at hodd'
      have hj0 : j = 0 := by
        rcases j with _ | j
        · rfl
        · exact absurd hodd' (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, by omega⟩))
      rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
      have hdvd := orderOf_dvd_of_pow_eq_one hj
      exact orderOf_dvd_iff_pow_eq_one.1 (hcop.symm.dvd_of_dvd_mul_left hdvd)
    · intro hk
      have : orderOf h₀ ∣ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨m, rfl⟩ := this
      rw [hs, ← pow_mul, show 2 ^ r * (orderOf h₀ * m) = orderOf h₀ * 2 ^ r * m by ring,
        pow_mul, pow_mul, ← hr, pow_orderOf_eq_one, one_pow]
  obtain ⟨h₁, hh₁, hcomm, μ, hμ, hscal⟩ := M.exists_scalar hsX (hNT1 s hsNT) hsa
    (hso ▸ hodd)
  exact ⟨h₁, hh₁.trans hso, hcomm, μ, hμ, hscal⟩

end ModConf

theorem LineConf.exists_modConf {a d x y : G} (C : LineConf D a d x y)
    (h3 : 3 ≤ (rootLines D a).ncard)
    (hN : Nat.card (lineN D a d) < Nat.card (rootGroup D a) ^ 6) :
    ∃ e : ℕ, e ≠ 0 ∧ Nat.card (rootGroup D a) = 2 ^ e ∧
      ∃ φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e),
      ∃ θ₀ θ₁ : (Fin 2 → GaloisField 2 e) → G, ModConf C φ θ₀ θ₁ := by
  have := C.finite
  obtain ⟨-, e, he, φ, hφx, hφy, hXN, hXN₀, -, hnorm, hcomm,
    ⟨m, Nf, θ, hNf, hθ, hsup, hcardN, -, hcardNd⟩, hgen⟩ :=
    rootLinesModuleStep G D C.setting a C.ha d C.hd C.had C.hadD C.hdT x C.hx C.hax C.haxD C.hxT
      y C.hy C.hdy C.hdyD C.hyT
  have hq2 : 2 ≤ Nat.card (rootGroup D a) := by
    have h1 : 1 < Nat.card (rootGroup D a) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      have haA : a ∈ rootGroup D a := rootSet_subset_rootGroup D a (mem_rootSet_self C.ha)
      rw [hbot, Subgroup.mem_bot] at haA
      exact C.root.ne_one C.ha haA
    omega
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    omega
  have hKq : Nat.card (GaloisField 2 e) = Nat.card (rootGroup D a) := by
    rw [GaloisField.card 2 e he0, he]
  have hm1 : m ≤ 1 := by
    have hTN₀ := Subgroup.card_dvd_of_le C.T_le_lineN₀
    rw [C.card_T] at hTN₀
    have h1 : Nat.card (rootGroup D a) ^ (2 + 2 * m) ≤ Nat.card (lineN D a d) := by
      rw [hcardN, pow_add]
      exact Nat.mul_le_mul_right _ (Nat.le_of_dvd Nat.card_pos hTN₀)
    have h2 := lt_of_le_of_lt h1 hN
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hcardNd
    have hNd : lineN₀ D a d = nCore D d ⊓ Subgroup.centralizer {a} :=
      Subgroup.eq_of_le_of_card_ge lineN₀_le_Nd hcardNd.le
    obtain ⟨k, hk, hkM⟩ := C.exists_mem_Nd_not_mem h3
    rw [← hNd] at hk
    exact hkM (Subgroup.mem_inf.1 hk).1
  obtain rfl : m = 1 := by omega
  have hNf0 : Nf 0 = lineN D a d := by
    rw [← hsup, iSup_unique, show (default : Fin 1) = 0 from rfl]
    exact (sup_eq_right.2 (hNf 0).1).symm
  have hθ₁ := (hNf 0).2
  rw [hNf0] at hθ₁
  obtain ⟨θ₀, hθ₀, hrange, ha0, hd0⟩ := C.exists_natural hKq φ hφx hφy
  exact ⟨e, he0, he, φ, θ₀, θ 0,
    { card_K := hKq
      map_x := hφx
      map_y := hφy
      conj_N := hXN
      conj_N₀ := hXN₀
      normal := hnorm
      comm := hcomm
      nat₀ := hθ₀
      range₀ := hrange
      axis_a := ha0
      axis_d := hd0
      nat₁ := hθ₁
      θ₁_a := fun s => (hθ 0 s).1
      θ₁_d := fun s => (hθ 0 s).2
      gen := hgen }⟩

end RootOne

end CFSG.Timmesfeld.Bridge
