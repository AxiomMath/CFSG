module

public import CFSG.OddTranspositions.ClassificationStatement
public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72

attribute [local instance] CFSG.LocalCores.layer_characteristic

variable {Y : Type} [Group Y] [Finite Y] {D : Set Y}

theorem isPGroup_quotient_layer_of_solvable
    (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g})
    (hroot : IsRootInvolutionSet D)
    (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4)
    (hgen : Subgroup.closure D = ⊤)
    (hnc : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y)
    (hchar : ∀ (N : Subgroup Y) [N.Characteristic], ¬ N ≤ Subgroup.center Y → IsPGroup 2 (Y ⧸ N)) :
    IsPGroup 2 ((Y ⧸ Subgroup.center Y) ⧸ layer (Y ⧸ Subgroup.center Y)) := by
  classical
  set Z : Subgroup Y := Subgroup.center Y with hZ
  set π : Y →* Y ⧸ Z := QuotientGroup.mk' Z with hπ
  set E : Subgroup (Y ⧸ Z) := layer (Y ⧸ Z) with hE
  haveI hEnormal : E.Normal := by
    rw [hE]
    infer_instance
  set Epre : Subgroup Y := E.comap π with hEpre
  have hGnt : Nontrivial (Y ⧸ Z) := by
    obtain ⟨d₀, hD⟩ := hcls
    have hd₀ : d₀ ∈ D := by rw [hD]; exact IsConj.refl d₀
    have hπd₀ : π d₀ ≠ 1 := by
      intro h
      exact hnc d₀ hd₀ ((QuotientGroup.eq_one_iff d₀).1 h)
    exact ⟨1, π d₀, fun h => hπd₀ h.symm⟩
  have hfit_le : fittingSubgroup (Y ⧸ Z) ≤ CFSG.solvableRadical (Y ⧸ Z) := by
    haveI hnil : Group.IsNilpotent (fittingSubgroup (Y ⧸ Z)) :=
      (CFSG.LocalCores.fitting_nilpotent (G := Y ⧸ Z)).1
    exact le_sSup ⟨inferInstance, inferInstance⟩
  haveI hRnorm : (CFSG.solvableRadical (Y ⧸ Z)).Normal :=
    Subgroup.sSup_normal _ fun _ hN => hN.1
  have hrad : CFSG.solvableRadical (Y ⧸ Z) = ⊥ :=
    solvable_normal_eq_bot_quotient_center (Y := Y) hsolv
      (CFSG.solvableRadical (Y ⧸ Z))
      (CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical (G := Y ⧸ Z))
  have hgf : CFSG.generalizedFitting (Y ⧸ Z) ≠ ⊥ :=
    (CFSG.LocalCores.generalized_fitting_minimal_normal (G := Y ⧸ Z)).2 hGnt
  have hEne : E ≠ ⊥ := by
    intro hEbot
    apply hgf
    rw [CFSG.generalizedFitting.eq_sup, ← hE, hEbot, sup_bot_eq]
    exact le_bot_iff.mp (hrad ▸ hfit_le)
  have hEchar : Epre.Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk (H := Z) (K := E)
      CFSG.LocalCores.layer_characteristic
  have hEnotle : ¬ Epre ≤ Z := by
    intro hle
    apply hEne
    have hmap : Epre.map π = E :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) E
    have hZmap : Z.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro z hz
      rw [MonoidHom.mem_ker, hπ, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff z).2 hz]
    have hle' : E ≤ ⊥ := by
      calc E = Epre.map π := hmap.symm
        _ ≤ Z.map π := Subgroup.map_mono hle
        _ = ⊥ := hZmap
    exact le_bot_iff.mp hle'
  haveI : Epre.Characteristic := hEchar
  have hY2 : IsPGroup 2 (Y ⧸ Epre) := hchar Epre hEnotle
  have hZle : Z ≤ Epre := by
    intro z hz
    rw [Subgroup.mem_comap]
    show π z ∈ E
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz]
    exact E.one_mem
  have hmap : Epre.map π = E :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) E
  have hthird : ((Y ⧸ Z) ⧸ Epre.map (QuotientGroup.mk' Z)) ≃* Y ⧸ Epre :=
    QuotientGroup.quotientQuotientEquivQuotient (N := Z) (M := Epre) hZle
  have hGE2 : IsPGroup 2 ((Y ⧸ Z) ⧸ E) :=
    (hY2.of_equiv hthird.symm).of_equiv
      (QuotientGroup.quotientMulEquivOfEq (show Epre.map (QuotientGroup.mk' Z) = E from hmap))
  exact hGE2

theorem commutator_eq_layer
    (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g})
    (hroot : IsRootInvolutionSet D)
    (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4)
    (hgen : Subgroup.closure D = ⊤)
    (hnc : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y)
    (hchar : ∀ (N : Subgroup Y) [N.Characteristic], ¬ N ≤ Subgroup.center Y → IsPGroup 2 (Y ⧸ N)) :
    commutator (Y ⧸ Subgroup.center Y) = layer (Y ⧸ Subgroup.center Y) := by
  classical
  set Z : Subgroup Y := Subgroup.center Y with hZ
  set E : Subgroup (Y ⧸ Z) := layer (Y ⧸ Z) with hE
  haveI hEnormal : E.Normal := by
    rw [hE]
    infer_instance
  have hGE2 : IsPGroup 2 ((Y ⧸ Z) ⧸ E) :=
    isPGroup_quotient_layer_of_solvable hcls hroot hdeg hgen hnc hsolv hchar
  set π : Y →* Y ⧸ Z := QuotientGroup.mk' Z with hπ
  set ψ : Y →* (Y ⧸ Z) ⧸ E := (QuotientGroup.mk' E).comp π with hψ
  set X : Set ((Y ⧸ Z) ⧸ E) := ψ '' D with hX
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective E).comp (QuotientGroup.mk'_surjective Z)
  have hXcl : Subgroup.closure X = ⊤ := by
    have h := MonoidHom.map_closure ψ D
    rw [hgen, Subgroup.map_top_of_surjective ψ hψsurj] at h
    exact h.symm
  have hcomm : X.Pairwise Commute := by
    rintro x hx y hy -
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨e, he, rfl⟩ := hy
    have hd2 : ψ d * ψ d = 1 := by
      rw [← map_mul, hroot.mul_self_eq_one hd, map_one]
    have he2 : ψ e * ψ e = 1 := by
      rw [← map_mul, hroot.mul_self_eq_one he, map_one]
    have hord2 : orderOf (ψ (d * e)) ∣ 2 := by
      have hdvd : orderOf (ψ (d * e)) ∣ orderOf (d * e) := orderOf_map_dvd ψ (d * e)
      obtain ⟨k, hk⟩ := hGE2.exists_orderOf_eq_pow (ψ (d * e))
      rcases hroot.2.1 d hd e he with h2 | h4 | hodd
      · rwa [h2] at hdvd
      · exact absurd h4 (hdeg d hd e he)
      · have hodd2 : Odd (2 ^ k) := hodd.of_dvd_nat (hk ▸ hdvd)
        have hk0 : k = 0 := by
          by_contra hk0
          exact (Nat.not_odd_iff_even.mpr (even_two.pow_of_ne_zero hk0)) hodd2
        rw [hk0, pow_zero] at hk
        rw [hk]
        exact one_dvd 2
    have hsq : (ψ d * ψ e) * (ψ d * ψ e) = 1 := by
      have h := orderOf_dvd_iff_pow_eq_one.mp hord2
      rwa [map_mul, pow_two] at h
    show Commute (ψ d) (ψ e)
    calc ψ d * ψ e = (ψ d * ψ e)⁻¹ := (inv_eq_of_mul_eq_one_right hsq).symm
      _ = (ψ e)⁻¹ * (ψ d)⁻¹ := mul_inv_rev _ _
      _ = ψ e * ψ d := by
        rw [inv_eq_of_mul_eq_one_right he2, inv_eq_of_mul_eq_one_right hd2]
  have hcommE : IsMulCommutative ((Y ⧸ Z) ⧸ E) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    have htop : IsMulCommutative (⊤ : Subgroup ((Y ⧸ Z) ⧸ E)) := by
      have h := Subgroup.isMulCommutative_closure hcomm
      rwa [hXcl] at h
    letI : IsMulCommutative (⊤ : Subgroup ((Y ⧸ Z) ⧸ E)) := htop
    exact congrArg Subtype.val
      (mul_comm' (⟨a, Subgroup.mem_top a⟩ : (⊤ : Subgroup ((Y ⧸ Z) ⧸ E)))
        ⟨b, Subgroup.mem_top b⟩)
  have hcomm_le : commutator (Y ⧸ Z) ≤ E :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := E)).mp hcommE
  have hE_le_comm : E ≤ commutator (Y ⧸ Z) := by
    rw [commutator_def]
    calc E = ⁅E, E⁆ := (CFSG.LocalCores.layer_perfect (G := Y ⧸ Z)).symm
      _ ≤ ⁅(⊤ : Subgroup (Y ⧸ Z)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
  have hEG : commutator (Y ⧸ Z) = E := le_antisymm hcomm_le hE_le_comm
  exact hEG

end CFSG.OddTranspositions
