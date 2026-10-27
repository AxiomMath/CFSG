module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.OddTranspositions.PartFour.Fourteen.OFour.PlusTau
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.LocalAnalysis.WeakClosure81
open CFSG.BenderSuzuki Matrix
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

variable {X : Type} [Group X]

section Wreath

variable {f : ℕ}

private theorem center_sl2_eq_bot {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Subgroup.mem_bot]
  have h2 : r ^ 2 = 1 := by simpa using hr
  have h : (r - 1) ^ 2 = 0 := by
    linear_combination h2 + (1 - r) * (CharP.cast_eq_zero K 2)
  have hr1 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  refine Subtype.ext ?_
  rw [← hrA, hr1, map_one]
  rfl

private noncomputable def psl2Equiv (f : ℕ) :
    PSL2Model f ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
  (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans QuotientGroup.quotientBot

private noncomputable def baseHom (f : ℕ) :
    (Fin 2 → PSL2Model f) →* GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f) :=
  jProd.comp
    { toFun := fun h => (psl2Equiv f (h 0), psl2Equiv f (h 1))
      map_one' := by simp [Prod.one_eq_mk]
      map_mul' := fun g h => by simp }

private theorem baseHom_apply (h : Fin 2 → PSL2Model f) :
    baseHom f h = j1 (psl2Equiv f (h 0)) * j2 (psl2Equiv f (h 1)) :=
  jProd_apply _ _

private theorem perm_two_cases (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  revert σ
  decide

private noncomputable def swapHom {F : Type} [Field F] :
    Equiv.Perm (Fin 2) →* GL (Fin 2 ⊕ Fin 2) F where
  toFun σ := if σ = 1 then 1 else tauMat
  map_one' := by simp
  map_mul' σ σ' := by
    rcases perm_two_cases σ with rfl | rfl <;> rcases perm_two_cases σ' with rfl | rfl
    · simp
    · simp
    · simp
    · simp [tauMat_mul_self]

private theorem swapHom_swap {F : Type} [Field F] :
    (swapHom (F := F)) (Equiv.swap 0 1) = tauMat := by
  simp [swapHom]

private theorem permAct_apply (σ : Equiv.Perm (Fin 2)) (h : Fin 2 → PSL2Model f) (i : Fin 2) :
    permAct (Fin 2) (PSL2Model f) σ h i = h (σ⁻¹ i) := rfl

private theorem baseHom_perm (σ : Equiv.Perm (Fin 2)) (h : Fin 2 → PSL2Model f) :
    baseHom f (permAct (Fin 2) (PSL2Model f) σ h) =
      swapHom σ * baseHom f h * (swapHom σ)⁻¹ := by
  rcases perm_two_cases σ with rfl | rfl
  · simp
  · rw [swapHom_swap, tauMat_inv, baseHom_apply, baseHom_apply, permAct_apply, permAct_apply]
    have h0 : (Equiv.swap (0 : Fin 2) 1)⁻¹ 0 = 1 := by decide
    have h1 : (Equiv.swap (0 : Fin 2) 1)⁻¹ 1 = 0 := by decide
    rw [h0, h1]
    set x := psl2Equiv f (h 0)
    set y := psl2Equiv f (h 1)
    have e : (tauMat : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) * (j1 x * j2 y) * tauMat =
        (tauMat * j1 x * tauMat) * (tauMat * j2 y * tauMat) := by
      calc _ = tauMat * j1 x * (tauMat * tauMat) * j2 y * tauMat := by
            rw [tauMat_mul_self, mul_one]
            simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    rw [e, tau_conj_j1, tau_conj_j2]
    exact (j1_j2_commute y x).eq

private noncomputable def wreathHom (f : ℕ) :
    L2Wreath f 2 →* GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f) :=
  SemidirectProduct.lift (baseHom f) swapHom (fun σ => by
    refine MonoidHom.ext fun h => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact baseHom_perm σ h)

private theorem wreathHom_apply (w : L2Wreath f 2) :
    wreathHom f w = baseHom f w.left * swapHom w.right := rfl

private theorem wreathHom_mem (w : L2Wreath f 2) :
    wreathHom f w ∈ CFSG.LieType.BorelTits.orthGroup
      (CFSG.Open.StatedQuadPlus 2 (GaloisField 2 f)) := by
  rw [wreathHom_apply]
  refine mul_mem ?_ ?_
  · rw [baseHom_apply]
    exact mul_mem (j1_mem_orthGroup _) (j2_mem_orthGroup _)
  · rcases perm_two_cases w.right with h | h
    · rw [h, map_one]
      exact one_mem _
    · rw [h, swapHom_swap]
      exact tauMat_mem_orthGroup

private theorem baseHom_injective : Function.Injective (baseHom f) := by
  intro g h hgh
  obtain ⟨h0, h1⟩ := Prod.ext_iff.mp (jProd_injective hgh)
  funext i
  fin_cases i
  · exact (psl2Equiv f).injective h0
  · exact (psl2Equiv f).injective h1

private theorem wreathHom_injective : Function.Injective (wreathHom f) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  rw [wreathHom_apply] at hw
  rcases perm_two_cases w.right with hr | hr
  · rw [hr, map_one, mul_one] at hw
    have hl : w.left = 1 := baseHom_injective (by rw [hw, map_one])
    exact SemidirectProduct.ext hl hr
  · exfalso
    rw [hr, swapHom_swap] at hw
    have : (tauMat : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) = (baseHom f w.left)⁻¹ :=
      eq_inv_of_mul_eq_one_right hw
    refine tauMat_not_mem_range (F := GaloisField 2 f) ?_
    rw [this]
    exact inv_mem ⟨_, rfl⟩

private theorem card_wreath (f : ℕ) :
    Nat.card (L2Wreath f 2) = Nat.card ↥(CFSG.LieType.BorelTits.orthGroup
      (CFSG.Open.StatedQuadPlus 2 (GaloisField 2 f))) := by
  rw [card_orthGroup_quadPlus_two, SemidirectProduct.card, Nat.card_fun, Nat.card_fin,
    Nat.card_congr (psl2Equiv f).toEquiv,
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell.card_SL2_eq]
  have hperm : Nat.card (Equiv.Perm (Fin 2)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [hperm]
  ring

private theorem exists_wreathEquiv (f : ℕ) :
    ∃ Φ : L2Wreath f 2 ≃* ↥(CFSG.PGLModel.orthogonalPlus 2 (GaloisField 2 f)),
      ∀ w, (Φ w : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) = wreathHom f w := by
  let Φ' : L2Wreath f 2 →* ↥(CFSG.PGLModel.orthogonalPlus 2 (GaloisField 2 f)) :=
    (wreathHom f).codRestrict (CFSG.PGLModel.orthogonalPlus 2 (GaloisField 2 f)) wreathHom_mem
  have hinj : Function.Injective Φ' := fun a b h => wreathHom_injective (congrArg Subtype.val h)
  have hbij : Function.Bijective Φ' :=
    (Nat.bijective_iff_injective_and_card Φ').2 ⟨hinj, card_wreath f⟩
  exact ⟨MulEquiv.ofBijective Φ' hbij, fun w => rfl⟩

private theorem center_eq_bot_of_equiv {H : Type*} [Group H] (hf : 2 ≤ f)
    (e : H ≃* L2Wreath f 2) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply e.injective
  rw [map_one]
  have hz' : e z ∈ Subgroup.center (L2Wreath f 2) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  have hcent : e z ∈ Subgroup.centralizer
      (CFSG.OddTranspositions.l2WreathBase f 2 : Set (L2Wreath f 2)) :=
    fun b _ => Subgroup.mem_center_iff.1 hz' b
  rw [CFSG.OddTranspositions.PartThree.centralizer_l2WreathBase hf] at hcent
  exact Subgroup.mem_bot.1 hcent

theorem eq_mk_of_mul_self_eq_one {w : L2Wreath f 2} (hw : w * w = 1)
    (hr : w.right ≠ 1) : w.right = Equiv.swap 0 1 ∧ w.left 1 = (w.left 0)⁻¹ := by
  have hr' : w.right = Equiv.swap 0 1 := (perm_two_cases w.right).resolve_left hr
  refine ⟨hr', ?_⟩
  have hl : (w * w).left = 1 := by rw [hw]; rfl
  rw [SemidirectProduct.mul_left] at hl
  have h0 := congrFun hl 0
  rw [Pi.mul_apply, permAct_apply, hr'] at h0
  have h1 : (Equiv.swap (0 : Fin 2) 1)⁻¹ 0 = 1 := by decide
  rw [h1] at h0
  exact eq_inv_of_mul_eq_one_right h0

private theorem rankOne_of_wreath_swap {w : L2Wreath f 2} (hw : w * w = 1)
    (hr : w.right ≠ 1) : IsRankOneIn (wreathHom f w) := by
  obtain ⟨hr', hl1⟩ := eq_mk_of_mul_self_eq_one hw hr
  have h : wreathHom f w = j1 (psl2Equiv f (w.left 0)) * tauMat *
      (j1 (psl2Equiv f (w.left 0)))⁻¹ := by
    rw [wreathHom_apply, baseHom_apply, hr', swapHom_swap, hl1, map_inv, mul_assoc,
      ← tauMat_mul_j1, ← mul_assoc, map_inv]
  rw [h]
  exact isRankOneIn_conj_tauMat (F := GaloisField 2 f) _

end Wreath

section Main

theorem right_ne_one_of_mem {E : Set X} (hS : Setup X E) {f : ℕ}
    (e : X ≃* L2Wreath f 2) {x : X} (hx : x ∈ E) : (e x).right ≠ 1 := by
  let N : Subgroup X := (SemidirectProduct.rightHom.comp e.toMonoidHom).ker
  have : N.Normal := MonoidHom.normal_ker _
  rcases hS.subset_or_disjoint N with h | h
  · exfalso
    have htop := hS.eq_top_of_subset N h
    have hmem : e.symm (SemidirectProduct.inr (Equiv.swap 0 1)) ∈ N := htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    simp at hmem
  · intro hr
    exact h x hx (by rw [MonoidHom.mem_ker]; exact hr)

end Main

theorem exists_isOrthReflection_of_mulEquiv_l2Wreath_two [Finite X] {E : Set X} (hS : Setup X E)
    {f : ℕ} (hf : 2 ≤ f) (e : X ≃* L2Wreath f 2) : ∃ s ∈ E, IsOrthReflection X 4 f s := by
  obtain ⟨s, hs⟩ := hS.nonempty
  obtain ⟨Φ, hΦ⟩ := exists_wreathEquiv f
  have hcenter : Subgroup.center X = ⊥ := center_eq_bot_of_equiv hf e
  have hss : s * s = 1 := by
    have h2 := hS.oddT.1 s hs
    have := pow_orderOf_eq_one s
    rwa [h2, pow_two] at this
  have hr : (e s).right ≠ 1 := right_ne_one_of_mem hS e hs
  have hww : e s * e s = 1 := by rw [← map_mul, hss, map_one]
  refine ⟨s, hs, Or.inl ⟨2, le_rfl, rfl, GaloisField 2 f, inferInstance, inferInstance,
    GaloisField.card 2 f (by omega), ?_⟩⟩
  let eQ : X ⧸ Subgroup.center X ≃* L2Wreath f 2 :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans e)
  refine ⟨eQ.trans Φ, ?_⟩
  have h : ((eQ.trans Φ) (QuotientGroup.mk s) : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) =
      wreathHom f (e s) := hΦ (e s)
  show IsRankOneIn ((eQ.trans Φ) (QuotientGroup.mk s) : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f))
  rw [h]
  exact rankOne_of_wreath_swap hww hr

end CFSG.OddTranspositions.PartFour
