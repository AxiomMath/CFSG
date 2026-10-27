module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.A5Irr
public import CFSG.GroupTheory.AlternatingFive.CommutingPair
public import CFSG.Quasithin.Background.F918Z0Mat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem exists_matModel_of_pair_irr {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L₁ L₂ X : Subgroup (MulAut W)} {I : Subgroup W} (hX : X = L₁ ⊔ L₂)
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (ha₁ : IsAlt ↥L₁ 5) (ha₂ : IsAlt ↥L₂ 5)
    (hI : IsIrrOn X I ⊥) (h₁ : commSub I L₁ ≠ ⊥) (h₂ : commSub I L₂ ≠ ⊥) :
    X ≤ stabSub I ∧ (∀ x ∈ X, (∀ u ∈ I, x u = u) → x = 1) ∧
      IsAlt ↥(autSub L₁ I) 5 ∧ IsAlt ↥(autSub L₂ I) 5 ∧
      autSub X I = autSub L₁ I ⊔ autSub L₂ I ∧
      (∀ g ∈ autSub L₁ I, ∀ x ∈ autSub L₂ I, g * x = x * g) ∧
      HasMatModel (autSub L₁ I) (autSub L₂ I) := by
  classical
  have hXstab : X ≤ stabSub I := B1.le_stabSub_of_invariant hI.2.1
  have hL₁X : L₁ ≤ X := hX ▸ le_sup_left
  have hL₂X : L₂ ≤ X := hX ▸ le_sup_right
  have hL₁stab : L₁ ≤ stabSub I := hL₁X.trans hXstab
  have hL₂stab : L₂ ≤ stabSub I := hL₂X.trans hXstab
  have hmv₁ : ∃ l ∈ L₁, ∃ u ∈ I, l u ≠ u := exists_moves_of_commSub_ne_bot h₁
  have hmv₂ : ∃ l ∈ L₂, ∃ u ∈ I, l u ≠ u := exists_moves_of_commSub_ne_bot h₂
  have hfaith₁ : ∀ l ∈ L₁, (∀ u ∈ I, l u = u) → l = 1 :=
    a5_faithful_of_moves ha₁ (fun l hl => hI.2.1 l (hL₁X hl)) hmv₁
  have hfaith₂ : ∀ l ∈ L₂, (∀ u ∈ I, l u = u) → l = 1 :=
    a5_faithful_of_moves ha₂ (fun l hl => hI.2.1 l (hL₂X hl)) hmv₂
  have hKle : X ⊓ centSub I ≤ L₁ ⊔ L₂ := by rw [← hX]; exact inf_le_left
  have hKn : ∀ k ∈ X ⊓ centSub I, ∀ x ∈ L₁ ⊔ L₂, x * k * x⁻¹ ∈ X ⊓ centSub I := by
    intro k hk x hx
    have hxX : x ∈ X := by rw [hX]; exact hx
    have hxstab : x ∈ stabSub I := hXstab hxX
    have hkfix : ∀ u ∈ I, k u = u := mem_centSub.mp hk.2
    refine ⟨X.mul_mem (X.mul_mem hxX hk.1) (X.inv_mem hxX), mem_centSub.mpr ?_⟩
    intro u hu
    have hxu : x⁻¹ u ∈ I := by
      have h := (mem_stabSub.mp hxstab) (x⁻¹ u)
      rw [show x (x⁻¹ u) = u from by simp] at h
      exact h.mp hu
    simp only [MulAut.mul_apply]
    rw [hkfix (x⁻¹ u) hxu]
    simp
  have hK₁ : (X ⊓ centSub I) ⊓ L₁ = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    exact hfaith₁ k hk.2 (fun u hu => mem_centSub.mp hk.1.2 u hu)
  have hK₂ : (X ⊓ centSub I) ⊓ L₂ = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    exact hfaith₂ k hk.2 (fun u hu => mem_centSub.mp hk.1.2 u hu)
  have hKbot : X ⊓ centSub I = ⊥ :=
    CFSG.GroupTheory.AlternatingFive.eq_bot_of_normal_of_inf_eq_bot hcomm ha₁ ha₂ hKle hKn hK₁ hK₂
  have hfaithX : ∀ x ∈ X, (∀ u ∈ I, x u = u) → x = 1 := by
    intro x hx hfix
    have hxK : x ∈ X ⊓ centSub I := ⟨hx, mem_centSub.mpr hfix⟩
    rw [hKbot, Subgroup.mem_bot] at hxK
    exact hxK
  have hAlt₁ : IsAlt ↥(autSub L₁ I) 5 := by
    obtain ⟨φ⟩ := ha₁
    exact ⟨(FFC.resEquiv hL₁stab hfaith₁).symm.trans φ⟩
  have hAlt₂ : IsAlt ↥(autSub L₂ I) 5 := by
    obtain ⟨φ⟩ := ha₂
    exact ⟨(FFC.resEquiv hL₂stab hfaith₂).symm.trans φ⟩
  have hAutSup : autSub X I = autSub L₁ I ⊔ autSub L₂ I := by
    unfold autSub
    rw [hX, Subgroup.subgroupOf_sup hL₁stab hL₂stab, Subgroup.map_sup]
  have hcommAut : ∀ g ∈ autSub L₁ I, ∀ x ∈ autSub L₂ I, g * x = x * g := by
    intro g hg x hx
    obtain ⟨g', hg'L, rfl⟩ := mem_autSub.mp hg
    obtain ⟨x', hx'L, rfl⟩ := mem_autSub.mp hx
    have hsub : g' * x' = x' * g' :=
      Subtype.ext (hcomm (g' : MulAut W) hg'L (x' : MulAut W) hx'L)
    calc resHom I g' * resHom I x' = resHom I (g' * x') := (map_mul (resHom I) g' x').symm
      _ = resHom I (x' * g') := by rw [hsub]
      _ = resHom I x' * resHom I g' := map_mul (resHom I) x' g'
  have hIne : I ≠ ⊥ := bot_lt_iff_ne_bot.mp hI.1
  haveI : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).mpr hIne
  have hMat : HasMatModel (autSub L₁ I) (autSub L₂ I) := by
    refine hasMatModel_of_irr (V := ↥I) (fun v : ↥I => ?_) hcommAut ?_
    · exact Subtype.ext (by simpa [pow_two] using hW (v : W))
    · intro U hU
      let J : Subgroup W := U.map I.subtype
      have hJstab : StableUnder X J := by
        intro x hx j hj
        obtain ⟨u, hu, rfl⟩ := hj
        have hxI : x ∈ stabSub I := hXstab hx
        have hg : resHom I ⟨x, hxI⟩ ∈ autSub X I :=
          mem_autSub.mpr ⟨⟨x, hxI⟩, hx, rfl⟩
        have hg' : resHom I ⟨x, hxI⟩ ∈ autSub L₁ I ⊔ autSub L₂ I := by
          rw [← hAutSup]
          exact hg
        have hmem : resHom I ⟨x, hxI⟩ u ∈ U := hU (resHom I ⟨x, hxI⟩) hg' u hu
        exact ⟨resHom I ⟨x, hxI⟩ u, hmem, resHom_apply I ⟨x, hxI⟩ u⟩
      rcases hI.2.2.2 J hJstab bot_le (Subgroup.map_subtype_le U) with hJ | hJ
      · left
        rw [eq_bot_iff]
        intro u hu
        rw [Subgroup.mem_bot]
        have hmem : (u : W) ∈ J := ⟨u, hu, rfl⟩
        rw [hJ, Subgroup.mem_bot] at hmem
        exact Subtype.ext (by simpa using hmem)
      · right
        rw [eq_top_iff]
        intro u _
        have hmem : (u : W) ∈ J := by rw [hJ]; exact u.2
        obtain ⟨u', hu', hval⟩ := hmem
        rwa [show u' = u from Subtype.ext hval] at hu'
  exact ⟨hXstab, hfaithX, hAlt₁, hAlt₂, hAutSup, hcommAut, hMat⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
