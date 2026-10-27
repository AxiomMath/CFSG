module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.AssocSup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.External
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Thm41AuxBasic

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm41Aux

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem hypC_of_mem_mhat
    (hθ : NearFunctor p A θ) {U : Subgroup G} (hU : U ∈ mhat p A θ) :
    HypC ↥U :=
  hypC_of_nearPSolvable hθ.prime hU.1.2.2.2.1

theorem kOf_mem_bTheta {U : Subgroup G} (hU : U ∈ mhat p A θ) : kOf U ∈ bTheta p A θ :=
  ⟨U, hU, kOf_le U, kOf_kOf U⟩

theorem key47
    (hθ : NearFunctor p A θ) {X : Subgroup G} (hX : X ∈ bTwo (bTheta p A θ))
    {Z U : Subgroup G} (hU : U ∈ mhat p A θ) (hZU : Z ≤ U)
    (hZ : (Z : Set G) * (sol X : Set G) = (X : Set G)) :
    (Z : Set G) * (sol U : Set G) = (kOf U : Set G) ∧ kOf U ∈ bTwo (bTheta p A θ) := by
  obtain ⟨⟨hXT, hXdeg⟩, hXcard⟩ := hX
  obtain ⟨V, hV, hXV, hXk⟩ := hXT
  have hXo : oStar ↥X = ⊤ := (kOf_eq_self_iff_oStar_eq_top X).mp hXk
  obtain ⟨hZX, hdegZX, hcardZX, hZo⟩ := mul_sol_eq_props hZ
  have hZo' : oStar ↥Z = ⊤ := hZo hXo
  have hC : HypC ↥U := hypC_of_mem_mhat hθ hU
  have hZ'b : Z.subgroupOf U ∈ bSet ↥U :=
    (kOf_eq_self_iff_oStar_eq_top _).mpr ((oStar_subgroupOf_eq_top_iff hZU).mpr hZo')
  have hdegZ' : deg ↥(Z.subgroupOf U) = deg ↥X := (deg_subgroupOf hZU).trans hdegZX
  have hKT : kOf U ∈ bTheta p A θ := kOf_mem_bTheta hU
  have hKdeg : deg ↥(oStar ↥U) ≤ deg ↥X := by
    rw [← deg_kOf]
    exact hXdeg _ hKT
  have hdeg1 : deg ↥(Z.subgroupOf U) ≤ deg ↥(oStar ↥U) :=
    BAux.deg_le_oStar_of_mem_bSet hC hZ'b
  have hdeg2 : deg ↥(oStar ↥U) ≤ deg ↥(Z.subgroupOf U) := by omega
  obtain ⟨hc1, hc2⟩ := BAux.card_quot_le_oStar hC hZ'b hdeg2
  have hKone : kOf U ∈ bOne (bTheta p A θ) :=
    ⟨hKT, fun Y hY => by
      rw [deg_kOf]
      have := hXdeg Y hY
      omega⟩
  have hc3 := hXcard _ hKone
  have e1 := (card_quot_subgroupOf hZU).trans hcardZX
  have e2 := card_quot_kOf U
  have hle2 : Nat.card (↥(oStar ↥U) ⧸ CFSG.solvableRadical ↥(oStar ↥U)) ≤
      Nat.card (↥(Z.subgroupOf U) ⧸ CFSG.solvableRadical ↥(Z.subgroupOf U)) := by omega
  refine ⟨mul_sol_eq_of_subgroupOf hZU (hc2 hle2), hKone, fun Y hY => ?_⟩
  have := hXcard Y hY
  omega

theorem exists_mem_bTheta_pos_deg (hθ : NearFunctor p A θ)
    (hns : ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a)) : ∃ Y ∈ bTheta p A θ, 0 < deg ↥Y := by
  obtain ⟨a, ha, ha1, hsol⟩ := hns
  have hV : θ a ∈ mhat p A θ := mtil_subset_mhat (apply_mem_mtil hθ ha ha1)
  refine ⟨kOf (θ a), kOf_mem_bTheta hV, ?_⟩
  rw [deg_kOf]
  exact pos_deg_oStar hsol

theorem not_isSolvable_of_mem_bOne (hθ : NearFunctor p A θ)
    (hns : ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a)) {X : Subgroup G}
    (hX : X ∈ bOne (bTheta p A θ)) : ¬ Group.IsSolvable X := by
  intro hs
  obtain ⟨Y, hY, hpos⟩ := exists_mem_bTheta_pos_deg hθ hns
  have h1 := hX.2 Y hY
  have h0 : deg ↥X = 0 := KAPI.deg_eq_zero_of_isSolvable hs
  omega

theorem bStarTheta_nonempty (hθ : NearFunctor p A θ)
    (hns : ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a)) : (bStarTheta p A θ).Nonempty := by
  obtain ⟨Y, hY, -⟩ := exists_mem_bTheta_pos_deg hθ hns
  exact bStar_nonempty ⟨Y, hY⟩

theorem isGreatest_sol (hθ : NearFunctor p A θ) {X : Subgroup G}
    (hb : ∀ Z ∈ mhat p A θ, ∀ U ∈ mhat p A θ,
      (Z : Set G) * (sol (kOf X) : Set G) = (kOf X : Set G) → Z ≤ U →
        (Z : Set G) * (sol U : Set G) = (kOf U : Set G))
    (hc : ∀ U ∈ mhat p A θ, kOf X ≤ U → kOf U = kOf X)
    {Z T : Subgroup G} (hZ : Z ∈ mhat p A θ) (hT : T ∈ mhat p A θ)
    (hZsol : (Z : Set G) * (sol X : Set G) = (kOf X : Set G))
    (hTs : Group.IsSolvable T) (hsolT : sol X ≤ T) :
    IsGreatest {M : Subgroup G | M ≤ T ∧ Admits Z M} (sol X) := by
  have hsolW : sol (kOf X) = sol X := sol_kOf_eq X
  have hZsolW : (Z : Set G) * (sol (kOf X) : Set G) = (kOf X : Set G) := by
    rw [hsolW]
    exact hZsol
  have hZW : Z ≤ kOf X := fun z hz => by
    have : z ∈ (Z : Set G) * (sol (kOf X) : Set G) := ⟨z, hz, 1, one_mem _, mul_one z⟩
    rw [hZsolW] at this
    exact this
  have hZXsol : Admits Z (sol X) := fun z hz =>
    le_normalizer_sol X ((kOf_le X) (hZW hz))
  refine ⟨⟨hsolT, hZXsol⟩, ?_⟩
  rintro M ⟨hMT, hZM⟩
  set S : Set (Subgroup G) := {M | M ≤ T ∧ Admits Z M} with hS
  set M₀ : Subgroup G := sSup S with hM₀
  refine (le_sSup ⟨hMT, hZM⟩ : M ≤ M₀).trans ?_
  have hM₀T : M₀ ≤ T := sSup_le fun M' hM' => hM'.1
  have hZM₀ : Admits Z M₀ := admits_sSup_of_forall fun z hz M' hM' => by
    rw [map_conj_eq_of_mem_normalizer (hM'.2 hz)]
    exact hM'
  have hDAZ : Admits (dsub A θ ⊔ A) Z := sup_le hZ.2 hZ.1.1
  have hDAT : Admits (dsub A θ ⊔ A) T := sup_le hT.2 hT.1.1
  have hDA : Admits (dsub A θ ⊔ A) M₀ := admits_sSup_of_forall fun q hq M' hM' =>
    map_conj_mem_of_admits (hDAZ hq) (hDAT hq) hM'
  have hM₀mhat : M₀ ∈ mhat p A θ := mem_mhat_of_le_mhat hθ.prime hT hM₀T hDA
  have hsolM₀ : sol X ≤ M₀ := le_sSup ⟨hsolT, hZXsol⟩
  have hUassoc : M₀ ⊔ Z ∈ assoc p A θ :=
    sup_mem_assoc hθ.prime hθ.elemAbelian hM₀mhat.1 hZ.1 hZM₀
  have hUmhat : M₀ ⊔ Z ∈ mhat p A θ := ⟨hUassoc, admits_sup (le_sup_left.trans hDA) hZ.2⟩
  have hWU : kOf X ≤ M₀ ⊔ Z := by
    intro w hw
    have : w ∈ (Z : Set G) * (sol (kOf X) : Set G) := by
      rw [hZsolW]
      exact hw
    obtain ⟨z, hz, s, hs, rfl⟩ := this
    have hsX : s ∈ sol X := by
      rw [← hsolW]
      exact hs
    exact mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left (hsolM₀ hsX))
  have hKU : kOf (M₀ ⊔ Z) = kOf X := hc _ hUmhat hWU
  have hZU : (Z : Set G) * (sol (M₀ ⊔ Z) : Set G) = (kOf (M₀ ⊔ Z) : Set G) :=
    hb Z hZ _ hUmhat hZsolW le_sup_right
  have hM₀sol : Group.IsSolvable M₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM₀T)
  have hM₀U : M₀ ≤ sol (M₀ ⊔ Z) :=
    le_sol_of_normal_solvable le_sup_left (sup_le Subgroup.le_normalizer hZM₀) hM₀sol
  have hUW : M₀ ⊔ Z ≤ kOf X := by
    refine sup_le (fun m hm => ?_) hZW
    have : m ∈ (Z : Set G) * (sol (M₀ ⊔ Z) : Set G) := ⟨1, one_mem Z, m, hM₀U hm, one_mul m⟩
    rw [hZU, hKU] at this
    exact this
  have hUeq : M₀ ⊔ Z = kOf X := le_antisymm hUW hWU
  have h5 : sol (M₀ ⊔ Z) = sol X := by rw [hUeq, hsolW]
  exact hM₀U.trans h5.le

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm41Aux
