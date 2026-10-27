module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.F6CatSetting

public section

namespace CFSG.Quasithin.F6

namespace G22M12Ident

open CFSG.RankThree.PartTwo.KFacts

section Action

variable {D : Type} [Group D]

@[expose] noncomputable def actL (t : D) : MulAut ↥(twoResidual (⊤ : Subgroup D)) :=
  haveI : (twoResidual (⊤ : Subgroup D)).Normal := twoResidual_top_normal
  MulAut.conjNormal t

theorem coe_actL (t : D) (l : ↥(twoResidual (⊤ : Subgroup D))) :
    ((actL t l : ↥(twoResidual (⊤ : Subgroup D))) : D) = t * l * t⁻¹ :=
  have : (twoResidual (⊤ : Subgroup D)).Normal := twoResidual_top_normal
  MulAut.conjNormal_apply t l

theorem actL_mul (t s : D) : actL (t * s) = actL t * actL s := by
  have : (twoResidual (⊤ : Subgroup D)).Normal := twoResidual_top_normal
  exact map_mul MulAut.conjNormal t s

theorem actL_coe (l : ↥(twoResidual (⊤ : Subgroup D))) : actL (l : D) = MulAut.conj l := by
  have : (twoResidual (⊤ : Subgroup D)).Normal := twoResidual_top_normal
  exact MulAut.conjNormal_val

theorem not_isInnerAut_actL [Finite D] (hS : F618RecogSetting D) {t : D}
    (ht : t ∉ twoResidual (⊤ : Subgroup D)) : ¬ IsInnerAut (actL t) := by
  rintro ⟨l, hl⟩
  apply ht
  have hxC : (l : D)⁻¹ * t ∈ Subgroup.centralizer (twoResidual (⊤ : Subgroup D) : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    have h1 := congrArg (fun f : MulAut ↥(twoResidual (⊤ : Subgroup D)) =>
      ((f ⟨l', hl'⟩ : ↥(twoResidual (⊤ : Subgroup D))) : D)) hl
    simp only [MulAut.conj_apply, coe_actL, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc l' * ((l : D)⁻¹ * t) = (l : D)⁻¹ * ((l : D) * l' * (l : D)⁻¹) * t := by group
      _ = (l : D)⁻¹ * (t * l' * t⁻¹) * t := by rw [h1]
      _ = (l : D)⁻¹ * t * l' := by group
  have hxL : (l : D)⁻¹ * t ∈ twoResidual (⊤ : Subgroup D) := by
    have h := CFSG.centralizer_generalizedFitting_le D
    rw [hS.fitting] at h
    exact h hxC
  have : t = (l : D) * ((l : D)⁻¹ * t) := by group
  rw [this]
  exact mul_mem l.2 hxL

theorem isInnerAut_actL_mul_self (hidx : (twoResidual (⊤ : Subgroup D)).index = 2) (t : D) :
    IsInnerAut (actL t * actL t) := by
  have : (twoResidual (⊤ : Subgroup D)).Normal := twoResidual_top_normal
  have h := Subgroup.pow_index_mem (twoResidual (⊤ : Subgroup D)) t
  rw [hidx, pow_two] at h
  refine ⟨⟨t * t, h⟩, ?_⟩
  rw [← actL_mul]
  exact (actL_coe ⟨t * t, h⟩).symm

theorem congr_actL_apply {G₀ : Type*} [Group G₀] (t : D) (e : ↥(twoResidual (⊤ : Subgroup D)) ≃* G₀)
    (n : ↥(twoResidual (⊤ : Subgroup D))) : MulAut.congr e (actL t) (e n) = e (actL t n) := by
  rw [MulAut.congr_apply]
  simp

theorem congr_actL_not_isInnerAut [Finite D] (hS : F618RecogSetting D) {t : D}
    (ht : t ∉ twoResidual (⊤ : Subgroup D)) {G₀ : Type*} [Group G₀]
    (e : ↥(twoResidual (⊤ : Subgroup D)) ≃* G₀) : ¬ IsInnerAut (MulAut.congr e (actL t)) :=
  fun h => not_isInnerAut_actL hS ht ((isInnerAut_congr e _).mp h)

theorem congr_actL_mul_self_isInnerAut (hidx : (twoResidual (⊤ : Subgroup D)).index = 2) (t : D)
    {G₀ : Type*} [Group G₀] (e : ↥(twoResidual (⊤ : Subgroup D)) ≃* G₀) :
    IsInnerAut (MulAut.congr e (actL t) * MulAut.congr e (actL t)) := by
  rw [← map_mul]
  exact (isInnerAut_congr e _).mpr (isInnerAut_actL_mul_self hidx t)

end Action

section Assembly

variable {D : Type} [Group D]

theorem lift_of_conj_eq {S Q : Type*} [Group S] [Group Q] (q : S →* Q) (Θ : MulAut S)
    (θ' : MulAut Q) (hθ' : ∀ s, θ' (q s) = q (Θ s)) (t : D)
    (e₀ : ↥(twoResidual (⊤ : Subgroup D)) ≃* Q) (ε : MulAut Q)
    (h : ε * MulAut.congr e₀ (actL t) * ε⁻¹ = θ')
    (n m : ↥(twoResidual (⊤ : Subgroup D))) (s : S)
    (hm : (m : D) = t * n * t⁻¹) (hn : (e₀.trans ε) n = q s) :
    (e₀.trans ε) m = q (Θ s) := by
  have hmn : m = actL t n := Subtype.ext (by rw [coe_actL]; exact hm)
  have h1 : (e₀.trans ε) m = (ε * MulAut.congr e₀ (actL t) * ε⁻¹) (ε (e₀ n)) := by
    rw [hmn]
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      congr_actL_apply]
  rw [h1, h, ← hθ']
  congr 1

theorem isExtendedByMatrixMap_of_lift {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {H Z₀ : Subgroup (GL ι F)} [(Z₀.subgroupOf H).Normal] (α : Matrix ι ι F → Matrix ι ι F)
    {W : Type*} [Group W] (N : Subgroup W) (hN : N.index = 2) {t : W} (ht : t ∉ N)
    (e : ↥N ≃* ↥H ⧸ Z₀.subgroupOf H) (Θ : MulAut ↥H) (g : ↥H)
    (hΘ : ∀ s : ↥H, (((Θ s : ↥H) : GL ι F) : Matrix ι ι F) =
      ((g : GL ι F) : Matrix ι ι F) * α ((s : GL ι F) : Matrix ι ι F) *
        (((g : GL ι F)⁻¹ : GL ι F) : Matrix ι ι F))
    (hlift : ∀ (n m : ↥N) (A : ↥H), (m : W) = t * n * t⁻¹ →
      e n = (QuotientGroup.mk A : ↥H ⧸ Z₀.subgroupOf H) →
      e m = (QuotientGroup.mk (Θ A) : ↥H ⧸ Z₀.subgroupOf H)) :
    IsExtendedByMatrixMap H Z₀ α W := by
  refine ⟨N, e, t, g, hN, ht, ?_⟩
  intro n m A B hm hA hB
  have hBΘ : B = Θ A := Subtype.ext (Units.ext (hB.trans (hΘ A).symm))
  rw [hBΘ]
  exact hlift n m A hm hA

end Assembly

end G22M12Ident

end CFSG.Quasithin.F6
