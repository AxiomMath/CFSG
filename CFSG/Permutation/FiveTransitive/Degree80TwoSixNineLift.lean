module

public import CFSG.Permutation.FiveTransitive.Degree80ThreeAmbientOrder
public import CFSG.Permutation.FiveTransitive.ThreeGroupSmallExponent

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoSixNineLift
open MulAction FixedNormalizerAction

private theorem three_not_dvd_kernel
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hF : Nat.card (Fixed (X := X) Q) = 6) :
    ¬ 3 ∣ Nat.card (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let rho := toPermHom (Normalizer Q) F
  intro hd
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := rho.ker) 3 hd
  have horder : orderOf g.val.val = 3 :=
    (Subgroup.orderOf_coe g.val).trans ((Subgroup.orderOf_coe g).trans hg)
  have hh := Degree80ThreeNoSixFixed.fixed_card_cases P hcard h5 hnotAlt g.val.val horder
  let f : F → Function.fixedPoints g.val.val.val := fun x =>
    ⟨x.val,congrArg Subtype.val (DFunLike.congr_fun (show rho g.val = 1 from g.property) x)⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun t : Function.fixedPoints g.val.val.val => t.val) h)
  have hb := Nat.card_le_card_of_injective f hf
  change Nat.card F = 6 at hF
  rw [hF] at hb
  omega

theorem exists_nine
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hF : Nat.card (Fixed (X := X) Q) = 6)
    (himage : Image (X := X) Q = ⊤) :
    ∃ H : Subgroup (Normalizer Q), IsPGroup 3 H ∧ Nat.card H = 9 ∧
      (∀ h : H, h ^ 3 = 1) ∧
      (∀ h : H, h ≠ 1 →
        (Nat.card (fixedBy (Fixed (X := X) Q) h) = 0 ∨
          Nat.card (fixedBy (Fixed (X := X) Q) h) = 3) ∧
        (Nat.card (fixedBy X h) = 2 ∨ Nat.card (fixedBy X h) = 5)) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let N := Normalizer Q
  let rho := toPermHom N F
  change Nat.card F = 6 at hF
  change rho.range = ⊤ at himage
  let S : Sylow 3 N := Sylow.nonempty.some
  let H : Subgroup N := S
  have hH : IsPGroup 3 H := S.isPGroup'
  have hdN : 9 ∣ Nat.card N := by
    have hd : 9 ∣ Nat.card rho.range := by
      rw [himage,Subgroup.card_top,Nat.card_perm,hF]
      norm_num [Nat.factorial]
    exact hd.trans (Subgroup.card_range_dvd rho)
  have hdH : 9 ∣ Nat.card H := S.pow_dvd_card_of_pow_dvd_card (n := 2) hdN
  have hnH : ¬ 27 ∣ Nat.card H := by
    intro hd
    exact Degree80ThreeAmbientOrder.twenty_seven_not_dvd_card P hcard h5 hnotAlt
      ((hd.trans (Subgroup.card_subgroup_dvd_card H)).trans (Subgroup.card_subgroup_dvd_card N))
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hH
  have he2 : e ≤ 2 := by
    by_contra hn
    apply hnH
    rw [he]
    exact pow_dvd_pow 3 (by omega : 3 ≤ e)
  have hc : Nat.card H = 9 := by
    have hl := Nat.le_of_dvd (show 0 < Nat.card H from Nat.card_pos) hdH
    have hu : Nat.card H ≤ 9 := by rw [he]; exact Nat.pow_le_pow_right (by decide) he2
    omega
  have hker := three_not_dvd_kernel P hcard h5 hnotAlt Q hF
  have hdis : Disjoint H rho.ker := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hc]
    exact ((Nat.prime_three.coprime_iff_not_dvd.mpr hker).pow_left 2)
  have hinj : Function.Injective (rho.comp H.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.eq_bot_iff_forall]
    intro h hh
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hdis.le_bot ⟨h.property,hh⟩)
  have hpow (h : H) : h ^ 3 = 1 := by
    apply hinj
    apply Equiv.ext
    intro x
    change h ^ 3 • x = x
    exact ThreeGroupSmallExponent.cube_smul hH (by omega) h x
  refine ⟨H,hH,hc,hpow,?_⟩
  intro h hh
  have horder : orderOf h = 3 := orderOf_eq_prime (hpow h) hh
  have horderP : orderOf h.val.val = 3 :=
    (Subgroup.orderOf_coe h.val).trans ((Subgroup.orderOf_coe h).trans horder)
  have hglobal := Degree80ThreeNoSixFixed.fixed_card_cases P hcard h5 hnotAlt h.val.val horderP
  change Nat.card (fixedBy X h) = 2 ∨ Nat.card (fixedBy X h) = 5 at hglobal
  have hlmod := PrimeNormalizerResidueObstruction.perm_fixed_card_modEq
    (toPermHom H F h) (by rw [← map_pow,hpow,map_one])
  change Nat.card F % 3 = Nat.card (fixedBy F h) % 3 at hlmod
  rw [hF] at hlmod
  let f : fixedBy F h → fixedBy X h := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun t : fixedBy X h => t.val) he))
  have hb := Nat.card_le_card_of_injective f hf
  have hlocal : Nat.card (fixedBy F h) = 0 ∨ Nat.card (fixedBy F h) = 3 := by omega
  exact ⟨hlocal,hglobal⟩

end FiveTransitive.Degree80TwoSixNineLift

end CFSG
