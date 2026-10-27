module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.Core

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab

variable {Γ : Type*} [Group Γ]

theorem mem_lcal_of_isSubnormal {X Y J : Subgroup Γ} (hJ : J ∈ lcal Y) (hYX : Y ≤ X)
    (hY : (Y.subgroupOf X).IsSubnormal) : J ∈ lcal X := by
  obtain ⟨hJY, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  refine mem_lcal_iff.mpr ⟨hJY.trans hYX, ?_, hs, hnc⟩
  let e := Subgroup.subgroupOfEquivOfLe hYX
  have heq : (J.subgroupOf X).subgroupOf (Y.subgroupOf X) =
      (J.subgroupOf Y).comap e.toMonoidHom := by
    ext x
    rfl
  refine Subgroup.IsSubnormal.trans (fun x hx => hJY hx) ?_ hY
  rw [heq]
  exact hsub.comap e.toMonoidHom

theorem map_mk'_mem_lcalOf {H : Type*} [Group H] {R : Subgroup H} [R.Normal] {C : Subgroup H}
    (hC : C ∈ lcalOf H) (hCR : C ⊓ R = ⊥) : C.map (QuotientGroup.mk' R) ∈ lcalOf (H ⧸ R) := by
  obtain ⟨hsub, hs, hnc⟩ := hC
  have hinj : Function.Injective ((QuotientGroup.mk' R).comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    have h1 : (c : H) ∈ R := by
      have := MonoidHom.mem_ker.mp hc
      rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have h2 : (c : H) ∈ C ⊓ R := Subgroup.mem_inf.mpr ⟨c.2, h1⟩
    rw [hCR, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  let e : ↥C ≃* ↥(C.map (QuotientGroup.mk' R)) :=
    MulEquiv.ofBijective (((QuotientGroup.mk' R).comp C.subtype).codRestrict
      (C.map (QuotientGroup.mk' R)) (fun c => ⟨c, c.2, rfl⟩))
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun y => by
        obtain ⟨c, hc, hcy⟩ := y.2
        exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩⟩
  exact ⟨hsub.map (QuotientGroup.mk'_surjective R), e.symm.isSimpleGroup,
    fun hc => hnc ((isMulCommutative_congr e).mpr hc)⟩

theorem sol_sup_mem_mcal {X C : Subgroup Γ} (hC : C ∈ lcal X) (hCS : C ⊓ sol X = ⊥) :
    sol X ⊔ C ∈ mcal X := by
  refine ⟨sup_le (sol_le X) hC.1, le_sup_left, ?_⟩
  rw [Subgroup.subgroupOf_sup (sol_le X) hC.1, subgroupOf_sol, Subgroup.map_sup]
  have h1 : (CFSG.solvableRadical ↥X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [h1, bot_sup_eq]
  refine map_mk'_mem_lcalOf hC.2 ?_
  rw [← subgroupOf_sol]
  have : C.subgroupOf X ⊓ (sol X).subgroupOf X = (C ⊓ sol X).subgroupOf X :=
    (Subgroup.comap_inf _ _ _).symm
  rw [this, hCS, Subgroup.bot_subgroupOf]

theorem mem_normalizer_of_mem_normalizer_sup {S C : Subgroup Γ} (hS : Group.IsSolvable S)
    (hs : IsSimpleGroup C) (hnc : ¬ IsMulCommutative C)
    (hcomm : ∀ s ∈ S, ∀ c ∈ C, Commute s c) (hSC : S ⊓ C = ⊥) {x : Γ}
    (hx : x ∈ Subgroup.normalizer ((S ⊔ C : Subgroup Γ) : Set Γ)) :
    x ∈ Subgroup.normalizer (C : Set Γ) := by
  have key : ∀ y ∈ Subgroup.normalizer ((S ⊔ C : Subgroup Γ) : Set Γ), ∀ c ∈ C,
      y * c * y⁻¹ ∈ C := by
    intro y hy c hc
    have := hs
    have hdp : IsDirectPair S C (S ⊔ C) := ⟨hcomm, hSC, rfl⟩
    let φ : ↥C →* ↥(S ⊔ C) :=
      ((S ⊔ C).normalizerMonoidHom ⟨y, hy⟩).toMonoidHom.comp (Subgroup.inclusion le_sup_right)
    let ψ : ↥C →* ↥S := (pairProj hdp).comp φ
    have hker : ψ.ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exfalso
        have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp h
        exact not_isSolvable_of_not_isMulCommutative hnc
          (Group.isSolvable_of_isSolvable_injective hinj)
      · exact h
    have h1 : ψ ⟨c, hc⟩ = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top _)
    obtain ⟨l, hl, hw⟩ := pairProj_spec hdp (φ ⟨c, hc⟩)
    have h2 : pairProj hdp (φ ⟨c, hc⟩) = 1 := h1
    rw [h2, Subgroup.coe_one, one_mul] at hw
    have h3 : ((φ ⟨c, hc⟩ : ↥(S ⊔ C)) : Γ) = y * c * y⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe (S ⊔ C) ⟨y, hy⟩
        ⟨c, (le_sup_right : C ≤ S ⊔ C) hc⟩
    rw [← h3, ← hw]
    exact hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key x hx c, fun h => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ h
  simpa [mul_assoc] using this

theorem mem_normalizer_of_mem_khat {X M : Subgroup Γ} (hX : ¬ Group.IsSolvable X)
    (hM : M ∈ mcal X) {x : Γ} (hx : x ∈ khat X) : x ∈ Subgroup.normalizer (M : Set Γ) := by
  have hMl : M ∈ ltilde X := Or.inr ⟨hX, hM⟩
  have h1 := (Subgroup.mem_inf.mp hx).2
  rw [Subgroup.mem_iInf] at h1
  have h2 := h1 M
  rw [Subgroup.mem_iInf] at h2
  exact h2 hMl

theorem mem_normalizer_of_mem_khat_of_mem_lcal [Finite Γ] {X C : Subgroup Γ}
    (hX : ¬ Group.IsSolvable X) (hC : C ∈ lcal X) (hcomm : ∀ s ∈ sol X, ∀ c ∈ C, Commute s c)
    {x : Γ} (hx : x ∈ khat X) : x ∈ Subgroup.normalizer (C : Set Γ) := by
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hC
  have hCS : sol X ⊓ C = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr ?_
    refine eq_one_of_forall_commute hnc hz.2 fun y hy => ?_
    exact (hcomm z hz.1 y hy).eq.symm
  have hM : sol X ⊔ C ∈ mcal X := sol_sup_mem_mcal hC (by rw [inf_comm]; exact hCS)
  exact mem_normalizer_of_mem_normalizer_sup (isSolvable_sol X) hs hnc hcomm hCS
    (mem_normalizer_of_mem_khat hX hM hx)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab
