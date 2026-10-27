module

public import CFSG.Quasithin.MS93.S33LamM

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.Explicit
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix IsMulCommutative

section Omega5

variable {F : Type} [Field F] [CharP F 2]

abbrev omComm (Γ : Subgroup (MSP.Sp4 F)) : Subgroup (Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)) :=
  Subgroup.closure {z | ∃ γ ∈ Γ, ∃ y, z = omega5Act F γ y * y⁻¹}

omit [CharP F 2] in
theorem omega5Act_transv_e₁ {d : F} (hd : d ≠ 0) :
    omega5Act F (MSP.transv (MSP.e₁ F) d⁻¹) (Multiplicative.ofAdd (d • MSP.f₁ F, 0)) *
        (Multiplicative.ofAdd (d • MSP.f₁ F, 0))⁻¹ =
      Multiplicative.ofAdd (MSP.e₁ F, d) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, omega5Act_toAdd, toAdd_ofAdd, toAdd_ofAdd]
  have hm : spMat (MSP.transv (MSP.e₁ F) d⁻¹) *ᵥ (d • MSP.f₁ F) = d • MSP.f₁ F + MSP.e₁ F := by
    change MSP.mat (MSP.transv (MSP.e₁ F) d⁻¹) *ᵥ (d • MSP.f₁ F) = _
    rw [MSP.transv_mulVec, MSP.form_e₁]
    simp [inv_mul_cancel₀ hd]
  rw [hm]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_add, Prod.snd_neg, neg_zero, add_zero, zero_add]
    simp [sp4Quad, MSP.e₁, MSP.f₁]

theorem rad_le_omComm_X₂ [Fintype F] (hF : 2 < Fintype.card F) :
    omega5Rad F ≤ omComm (MSP.X₂ F) := by
  intro y hy
  have hy1 : (Multiplicative.toAdd y).1 = 0 := hy
  set u := (Multiplicative.toAdd y).2
  have hyu : y = Multiplicative.ofAdd ((0 : Fin 2 ⊕ Fin 2 → F), u) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact Prod.ext hy1 rfl
  obtain ⟨d, hd0, hdu⟩ : ∃ d : F, d ≠ 0 ∧ d ≠ u := by
    classical
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset F) ⊆ {0, u} := fun s _ => by
      by_cases hs : s = 0
      · simp [hs]
      · simp [hall s hs]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h2 : ({0, u} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  have hd' : d + u ≠ 0 := by
    intro h0
    apply hdu
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
    exact h0
  have hmem : ∀ c : F, c ≠ 0 → Multiplicative.ofAdd (MSP.e₁ F, c) ∈ omComm (MSP.X₂ F) := by
    intro c hc
    rw [← omega5Act_transv_e₁ hc]
    exact Subgroup.subset_closure ⟨_, MSP.transv_mem_X₂ c⁻¹, _, rfl⟩
  have e : y = Multiplicative.ofAdd (MSP.e₁ F, d) * Multiplicative.ofAdd (MSP.e₁ F, d + u) := by
    rw [hyu]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      exact (CharTwo.add_self_eq_zero _).symm
    · simp only [Prod.snd_add]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [e]
  exact mul_mem (hmem d hd0) (hmem _ hd')

theorem rad_le_omComm_xPoint [Fintype F] (hF : 2 < Fintype.card F)
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) :
    omega5Rad F ≤ omComm (MSP.xPoint p) := by
  obtain ⟨g, rfl⟩ := MSP.exists_map_pt₀_eq hp
  let φ : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) →* Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) :=
    { toFun := omega5Act F g
      map_one' := by
        have h := omega5Act_mul g (1 : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)) 1
        rw [mul_one] at h
        exact (mul_eq_left.1 h.symm)
      map_mul' := omega5Act_mul g }
  have hle : (omComm (MSP.X₂ F)).map φ ≤ omComm (MSP.xPoint ((MSP.pt₀ F).map
      (MSP.mat g).mulVecLin)) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨t, ht, y, rfl⟩, rfl⟩
    have ht' : g * t * g⁻¹ ∈ MSP.xPoint ((MSP.pt₀ F).map (MSP.mat g).mulVecLin) := by
      rw [← MSP.X₂_map_conj]
      exact ⟨t, ht, rfl⟩
    refine Subgroup.subset_closure ⟨_, ht', omega5Act F g y, ?_⟩
    show omega5Act F g (omega5Act F t y * y⁻¹) = _
    have e1 : omega5Act F (g * t * g⁻¹) (omega5Act F g y) = omega5Act F g (omega5Act F t y) := by
      rw [← omega5Act_mul_act, ← omega5Act_mul_act]
      congr 1
      group
    have e2 : omega5Act F g y⁻¹ = (omega5Act F g y)⁻¹ := φ.map_inv y
    rw [omega5Act_mul, e1, e2]
  intro y hy
  have hy' : φ y = y := omega5Act_rad g hy
  rw [← hy']
  exact hle ⟨y, rad_le_omComm_X₂ hF hy, rfl⟩

end Omega5

section Lam

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {A : Subgroup G} {α : ↥A →* ↥(StatedSp 2 F)}
  {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → MSP.V4 F)}

variable (h : PUHyp M T L) (hAM : A ≤ M) (hβ : Function.Surjective β)
  (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
  (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec)
include h hAM hβ hβker hAβ

theorem exists_omega5_cover [CharP F 2] {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card F = 2 ^ k)
    (hLA : L ≤ A) (hα : Function.Surjective α)
    (hCfix : ∀ a ∈ A, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z) :
    ∃ ψ : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) →* ↥(Uq M T L), Function.Surjective ψ ∧
      (∀ (a : ↥A) (w : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)),
        ((ψ (omega5Act F (α a) w) : ↥(Uq M T L)) : G) = a * ψ w * (a : G)⁻¹) ∧
      ∀ w, ((ψ w : ↥(Uq M T L)) : G) ∈ Zq M L → w ∈ omega5Rad F := by
  have := Sp4L.isMulCommutative_uq h
  have hAV : A ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hAM.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨π, hπs, hπa⟩ := exists_pi_of_ker hAV hα fun a ha =>
    centralizer_of_eq_one h hAM hβ hβker hAβ ha
  have hnat := isSumOfNaturalModulesVia_of_coord hAV inf_le_left β hβ hβker hAβ
  have hreal := realizesVia_nat_of hAV hα hnat ((hAM.trans (le_normalizer_Uq_inf_Zq h)))
    hπs hπa
  have hZ : (Zq M L).subgroupOf (Uq M T L) ≤ fixV (autOn A (Uq M T L)) := by
    intro z hz x hx
    obtain ⟨g, hgA, rfl⟩ := Setup.mem_autOn_iff.1 hx
    apply Subtype.ext
    rw [InternalSec.coe_conjAct_apply]
    exact hCfix _ hgA _ ⟨z.2, Subgroup.mem_subgroupOf.1 hz⟩
  have hUA : ⁅Uq M T L, A⁆ = Uq M T L :=
    le_antisymm (commutator_le_left_of_le_normalizer hAV)
      (h.commutator_uq.symm.le.trans (Subgroup.commutator_mono le_rfl hLA))
  have hcomm : commV (autOn A (Uq M T L)) = ⊤ := InternalSec.commV_autOn_eq_top hAV hUA
  have hW : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using Sp4L.uq_sq h w.2)
  have hFn : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨ψ, hψs, hψe, hψZ⟩ := exists_omega5_quotient hFn hk hW hZ hcomm hreal
  refine ⟨ψ, hψs, fun a w => ?_, fun w hw => hψZ w (Subgroup.mem_subgroupOf.2 hw)⟩
  rw [hψe, hπa, InternalSec.coe_conjAct_apply]

omit [Finite G] [Fintype F] h hAM hβ hβker hAβ in
theorem map_omComm_le [CharP F 2] {ψ : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) →* ↥(Uq M T L)}
    (hψe : ∀ (a : ↥A) (w : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)),
      ((ψ (omega5Act F (α a) w) : ↥(Uq M T L)) : G) = a * ψ w * (a : G)⁻¹)
    {E : Subgroup G} {p : Submodule F (MSP.V4 F)} (hpE : MSP.xPoint p ≤ (E.subgroupOf A).map α)
    {w : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)} (hw : w ∈ omComm (MSP.xPoint p)) :
    ((ψ w : ↥(Uq M T L)) : G) ∈ ⁅Uq M T L, E⁆ := by
  have himage : (omComm (MSP.xPoint p)).map ψ ≤ (⁅Uq M T L, E⁆).subgroupOf (Uq M T L) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨γ, hγ, y, rfl⟩, rfl⟩
    obtain ⟨e, he, rfl⟩ := hpE hγ
    show ((ψ (omega5Act F (α e) y * y⁻¹) : ↥(Uq M T L)) : G) ∈ ⁅Uq M T L, E⁆
    rw [map_mul, map_inv, Subgroup.coe_mul, hψe, Subgroup.coe_inv, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 he) (ψ y).2
  exact Subgroup.mem_subgroupOf.1 (himage ⟨w, hw, rfl⟩)

theorem zq_le_commutator_of_xPoint [CharP F 2] {k : ℕ} (hk : 2 ≤ k)
    (hcard : Fintype.card F = 2 ^ k) (hLA : L ≤ A) (hα : Function.Surjective α)
    (hCfix : ∀ a ∈ A, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z) {E : Subgroup G}
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hpE : MSP.xPoint p ≤ (E.subgroupOf A).map α) :
    Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, E⁆ := by
  obtain ⟨ψ, hψs, hψe, hψZ⟩ :=
    exists_omega5_cover h hAM hβ hβker hAβ (by omega) hcard hLA hα hCfix
  have hF3 : 2 < Fintype.card F := by
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rintro z ⟨hzU, hzZ⟩
  obtain ⟨y, hy⟩ := hψs ⟨z, hzU⟩
  have hyR : y ∈ omega5Rad F := hψZ y (by rw [hy]; exact hzZ)
  have h1 := map_omComm_le hψe hpE (rad_le_omComm_xPoint hF3 hp hyR)
  rwa [hy] at h1

omit [Fintype F] in
theorem commutator_le_sup_of_commSp {E : Subgroup G} (hEA : E ≤ A) {Y : Subgroup G}
    (hYA : Y ≤ A) (hY : ∀ y ∈ (Y.subgroupOf A).map α, ∀ v : MSP.V4 F,
      MSP.mat y *ᵥ v - v ∈ MSP.commSp ((E.subgroupOf A).map α)) :
    ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆ ⊔ (Uq M T L ⊓ Zq M L) := by
  rw [Subgroup.commutator_le]
  intro u hu y hy
  have hyV : y * u * y⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer (hAM (hYA hy))) u).1 hu
  set c := natCoordOf β hβ hβker hAβ with hc
  have hmem : c.vec ⟨y * u * y⁻¹ * u⁻¹, mul_mem hyV (inv_mem hu)⟩ ∈
      MSP.commSp ((E.subgroupOf A).map α) := by
    rw [c.vec_commutator ⟨y, hYA hy⟩ ⟨u, hu⟩ hyV]
    exact hY _ ⟨⟨y, hYA hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩ _
  obtain ⟨r, hr, hrv⟩ := (mem_commSp_iff_crd h hAM hβ hβker hAβ hEA _).1 hmem
  have hz : c.vec (⟨y * u * y⁻¹ * u⁻¹, mul_mem hyV (inv_mem hu)⟩ * r⁻¹) = 0 := by
    rw [c.vec_mul, c.vec_inv, ← hrv]
    exact add_neg_cancel (Multiplicative.toAdd (β r) 0)
  rw [c.vec_eq_zero_iff] at hz
  have e : ⁅u, y⁆ = ((y * u * y⁻¹ * u⁻¹) * (r : G)⁻¹ * r)⁻¹ := by
    rw [inv_mul_cancel_right, commutatorElement_def]
    group
  rw [e]
  refine inv_mem (Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hr))
  exact hz

theorem commutator_le_of_commSp [CharP F 2] {k : ℕ} (hk : 2 ≤ k)
    (hcard : Fintype.card F = 2 ^ k) (hLA : L ≤ A) (hα : Function.Surjective α)
    (hCfix : ∀ a ∈ A, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z) {E : Subgroup G} (hEA : E ≤ A)
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hpE : MSP.xPoint p ≤ (E.subgroupOf A).map α) {Y : Subgroup G} (hYA : Y ≤ A)
    (hY : ∀ y ∈ (Y.subgroupOf A).map α, ∀ v : MSP.V4 F,
      MSP.mat y *ᵥ v - v ∈ MSP.commSp ((E.subgroupOf A).map α)) :
    ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆ :=
  (commutator_le_sup_of_commSp h hAM hβ hβker hAβ hEA hYA hY).trans (sup_le le_rfl
    (zq_le_commutator_of_xPoint h hAM hβ hβker hAβ hk hcard hLA hα hCfix hp hpE))

end Lam

end CFSG.Quasithin.MS93.S33
