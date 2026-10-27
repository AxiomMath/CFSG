module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggTP_card_ker_comp {G H K : Type*} [Group G] [Group H] [Group K] [Finite G]
    {f : G →* H} {g : H →* K} (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker := by
  have hH : Finite H := Finite.of_surjective f hf
  have hK : Finite K := Finite.of_surjective g hg
  have hgf : Function.Surjective (g.comp f) := by simpa using hg.comp hf
  have h1 := Subgroup.card_ker_mul_card_of_surjective (f := g.comp f) hgf
  have h2 := Subgroup.card_ker_mul_card_of_surjective (f := f) hf
  have h3 := Subgroup.card_ker_mul_card_of_surjective (f := g) hg
  have hKpos : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hKpos ?_
  calc
    Nat.card (g.comp f).ker * Nat.card K = Nat.card G := h1
    _ = Nat.card f.ker * Nat.card H := h2.symm
    _ = Nat.card f.ker * (Nat.card g.ker * Nat.card K) := by rw [← h3]
    _ = (Nat.card f.ker * Nat.card g.ker) * Nat.card K := by ring

theorem ggTPLift {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL ι K)) (hZ : ¬ 3 ∣ Nat.card ((LargeEvenScalars ι K).subgroupOf H))
    {G : Type} [Group G] [Finite G] {J K' : Subgroup G} (hJK : J ≤ K')
    (e : ↥K' ⧸ Subgroup.center ↥K' ≃* LargeEvenProj H) (hJ : CFSG.Assembly.IsQuasisimple ↥J)
    (hZJ : ¬ 3 ∣ Nat.card (Subgroup.center ↥J)) :
    ∃ (X : Subgroup (GL ι K)) (π : ↥X →* ↥J ⧸ Subgroup.center ↥J), X ≤ H ∧
      Function.Surjective π ∧ ¬ 3 ∣ Nat.card π.ker := by
  let Z₀ : Subgroup ↥H := (LargeEvenScalars ι K).subgroupOf H
  let j : ↥J →* LargeEvenProj H :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥K')).comp (Subgroup.inclusion hJK))
  let Ī : Subgroup (LargeEvenProj H) := j.range
  let Ĩ : Subgroup ↥H := Ī.comap (QuotientGroup.mk' Z₀)
  let X₀ : Subgroup ↥H := ⁅Ĩ, Ĩ⁆
  have hjk : j.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : (QuotientGroup.mk' (Subgroup.center ↥K')) (Subgroup.inclusion hJK x) = 1 := by
      have hxj : e ((QuotientGroup.mk' (Subgroup.center ↥K'))
          (Subgroup.inclusion hJK x)) = e 1 := by
        rw [map_one]
        simpa [j] using hx
      exact e.injective hxj
    have hx2 : Subgroup.inclusion hJK x ∈ Subgroup.center ↥K' := by
      rw [← QuotientGroup.ker_mk' (N := Subgroup.center ↥K')]
      exact MonoidHom.mem_ker.mpr hx1
    rw [Subgroup.mem_center_iff]
    intro y
    have hc := (Subgroup.mem_center_iff.mp hx2) (Subgroup.inclusion hJK y)
    exact Subgroup.inclusion_injective hJK (by simpa only [map_mul] using hc)
  have hIperf : ⁅Ī, Ī⁆ = Ī := by
    haveI : Group.IsPerfect ↥J := Group.IsPerfect.mk hJ.1
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (f := j))
  have hmapI : Ĩ.map (QuotientGroup.mk' Z₀) = Ī :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z₀) Ī
  have hX0map : X₀.map (QuotientGroup.mk' Z₀) = Ī := by
    change (⁅Ĩ, Ĩ⁆).map (QuotientGroup.mk' Z₀) = Ī
    rw [Subgroup.map_commutator Ĩ Ĩ (QuotientGroup.mk' Z₀), hmapI, hIperf]
  let f0 : ↥X₀ →* LargeEvenProj H := (QuotientGroup.mk' Z₀).comp X₀.subtype
  have hf0range : f0.range = Ī := by
    change ((QuotientGroup.mk' Z₀).comp X₀.subtype).range = Ī
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hX0map]
  have hf0ker : f0.ker = Z₀.subgroupOf X₀ := by
    change ((QuotientGroup.mk' Z₀).comp X₀.subtype).ker = Z₀.subgroupOf X₀
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hcenterker : j.ker ≤ (QuotientGroup.mk' (Subgroup.center ↥J)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hjk
  let g1 : ↥J ⧸ j.ker →* ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.lift j.ker (QuotientGroup.mk' (Subgroup.center ↥J)) hcenterker
  have hg1surj : Function.Surjective g1 := by
    have hcomp : g1.comp (QuotientGroup.mk' j.ker) = QuotientGroup.mk' (Subgroup.center ↥J) := by
      change (QuotientGroup.lift j.ker (QuotientGroup.mk' (Subgroup.center ↥J)) hcenterker).comp
          (QuotientGroup.mk' j.ker) = QuotientGroup.mk' (Subgroup.center ↥J)
      rw [QuotientGroup.lift_comp_mk']
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) y
    refine ⟨QuotientGroup.mk' j.ker x, ?_⟩
    change (g1.comp (QuotientGroup.mk' j.ker)) x = (QuotientGroup.mk' (Subgroup.center ↥J)) x
    rw [hcomp]
  have hg1ker : g1.ker = (Subgroup.center ↥J).map (QuotientGroup.mk' j.ker) := by
    change (QuotientGroup.lift j.ker (QuotientGroup.mk' (Subgroup.center ↥J)) hcenterker).ker
        = Subgroup.map (QuotientGroup.mk' j.ker) (Subgroup.center ↥J)
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  let ee : ↥J ⧸ j.ker ≃* Ī := QuotientGroup.quotientKerEquivRange j
  let g2 : Ī →* ↥J ⧸ Subgroup.center ↥J := g1.comp ee.symm.toMonoidHom
  have hg2surj : Function.Surjective g2 := hg1surj.comp ee.symm.surjective
  have hg2ker_dvd : Nat.card g2.ker ∣ Nat.card (Subgroup.center ↥J) := by
    have h1 : g2.ker = Subgroup.comap ee.symm.toMonoidHom g1.ker := by
      change (g1.comp ee.symm.toMonoidHom).ker = Subgroup.comap ee.symm.toMonoidHom g1.ker
      rw [MonoidHom.comap_ker]
    rw [h1]
    refine dvd_trans (Subgroup.card_comap_dvd_of_injective g1.ker ee.symm.toMonoidHom
      ee.symm.injective) ?_
    rw [hg1ker]
    exact Subgroup.card_map_dvd (Subgroup.center ↥J) (QuotientGroup.mk' j.ker)
  let f : ↥X₀ →* ↥f0.range := f0.rangeRestrict
  have hfsurj : Function.Surjective f := MonoidHom.rangeRestrict_surjective f0
  have hfker : f.ker = f0.ker := MonoidHom.ker_rangeRestrict f0
  let iso : ↥f0.range ≃* Ī := MulEquiv.subgroupCongr hf0range
  let g2' : ↥f0.range →* ↥J ⧸ Subgroup.center ↥J := g2.comp iso.toMonoidHom
  have hg2'surj : Function.Surjective g2' := hg2surj.comp iso.surjective
  have hg2'ker_dvd : Nat.card g2'.ker ∣ Nat.card (Subgroup.center ↥J) := by
    have h1 : g2'.ker = Subgroup.comap iso.toMonoidHom g2.ker := by
      change (g2.comp iso.toMonoidHom).ker = Subgroup.comap iso.toMonoidHom g2.ker
      rw [MonoidHom.comap_ker]
    rw [h1]
    exact dvd_trans (Subgroup.card_comap_dvd_of_injective g2.ker iso.toMonoidHom
      iso.injective) hg2ker_dvd
  let π0 : ↥X₀ →* ↥J ⧸ Subgroup.center ↥J := g2'.comp f
  have hπ0surj : Function.Surjective π0 := hg2'surj.comp hfsurj
  haveI : Finite ↥X₀ := inferInstance
  have hπ0card : Nat.card π0.ker = Nat.card f.ker * Nat.card g2'.ker := by
    change Nat.card (g2'.comp f).ker = Nat.card f.ker * Nat.card g2'.ker
    exact ggTP_card_ker_comp hfsurj hg2'surj
  have hfnot : ¬ 3 ∣ Nat.card f.ker := by
    have hd : Nat.card f.ker ∣ Nat.card Z₀ := by
      rw [hfker, hf0ker]
      exact Subgroup.card_comap_dvd_of_injective Z₀ X₀.subtype X₀.subtype_injective
    exact fun h => hZ (dvd_trans h hd)
  have hgnot : ¬ 3 ∣ Nat.card g2'.ker := fun h => hZJ (dvd_trans h hg2'ker_dvd)
  have hπ0not : ¬ 3 ∣ Nat.card π0.ker := by
    intro h3
    rw [hπ0card, Nat.Prime.dvd_mul Nat.prime_three] at h3
    exact h3.elim hfnot hgnot
  let X : Subgroup (GL ι K) := X₀.map H.subtype
  have hXle : X ≤ H := Subgroup.map_subtype_le X₀
  let κ : ↥X₀ ≃* ↥X := Subgroup.equivMapOfInjective X₀ H.subtype H.subtype_injective
  let π : ↥X →* ↥J ⧸ Subgroup.center ↥J := π0.comp κ.symm.toMonoidHom
  have hπsurj : Function.Surjective π := hπ0surj.comp κ.symm.surjective
  have hπker_dvd : Nat.card π.ker ∣ Nat.card π0.ker := by
    have h1 : π.ker = Subgroup.comap κ.symm.toMonoidHom π0.ker := by
      change (π0.comp κ.symm.toMonoidHom).ker = Subgroup.comap κ.symm.toMonoidHom π0.ker
      rw [MonoidHom.comap_ker]
    rw [h1]
    exact Subgroup.card_comap_dvd_of_injective π0.ker κ.symm.toMonoidHom κ.symm.injective
  have hπnot : ¬ 3 ∣ Nat.card π.ker := fun h => hπ0not (dvd_trans h hπker_dvd)
  exact ⟨X, π, hXle, hπsurj, hπnot⟩

end CFSG.StandardType

end
