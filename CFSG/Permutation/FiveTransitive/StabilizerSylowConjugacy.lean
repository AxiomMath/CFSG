module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.StabilizerSylowConjugacy

open MulAction

theorem exists_conjugating_transporter
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    {p : ℕ} [Fact p.Prime] (x y : X) (hxy : ∃ a:G,a • x=y)
    (P : Sylow p (stabilizer G x)) (S : Sylow p (stabilizer G y)) :
    ∃ a:G,a • x=y ∧
      ((P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype).map
        (MulAut.conj a).toMonoidHom =
      (S : Subgroup (stabilizer G y)).map (stabilizer G y).subtype := by
  obtain ⟨a,ha⟩ := hxy
  let E : stabilizer G x ≃* stabilizer G y := stabilizerEquivStabilizer ha.symm
  let T : Sylow p (stabilizer G y) := Sylow.mapSurjective (f:=E.toMonoidHom) E.surjective P
  obtain ⟨b,hb⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M:=stabilizer G y) (α:=Sylow p (stabilizer G y)) T S
  let z:G := (b:G)*a
  have hT : (T : Subgroup (stabilizer G y)).map (stabilizer G y).subtype =
      ((P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype).map
        (MulAut.conj a).toMonoidHom := by
    change ((P : Subgroup (stabilizer G x)).map E.toMonoidHom).map (stabilizer G y).subtype = _
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
  have hbmap : ((T : Subgroup (stabilizer G y)).map (stabilizer G y).subtype).map
      (MulAut.conj (b:G)).toMonoidHom =
      (S : Subgroup (stabilizer G y)).map (stabilizer G y).subtype := by
    calc
      _ = ((b • T : Sylow p (stabilizer G y)) : Subgroup (stabilizer G y)).map
          (stabilizer G y).subtype := by
        change ((T : Subgroup (stabilizer G y)).map (stabilizer G y).subtype).map
            (MulAut.conj (b:G)).toMonoidHom =
          ((T : Subgroup (stabilizer G y)).map (MulAut.conj b).toMonoidHom).map
            (stabilizer G y).subtype
        rw [Subgroup.map_map,Subgroup.map_map]
        congr 1
      _ = _ := by rw [hb]
  refine ⟨z,?_,?_⟩
  · change ((b:G)*a) • x=y
    rw [mul_smul,ha]
    exact b.property
  · calc
      _ = (((P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype).map
          (MulAut.conj a).toMonoidHom).map (MulAut.conj (b:G)).toMonoidHom := by
        have hcomp : (MulAut.conj z).toMonoidHom =
            (MulAut.conj (b:G)).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
          ext q
          change ((b:G)*a)*q*((b:G)*a)⁻¹ = (b:G)*(a*q*a⁻¹)*(b:G)⁻¹
          group
        simp only [hcomp,Subgroup.map_map,MonoidHom.comp_assoc]
      _ = _ := by rw [←hT]; exact hbmap

end FiveTransitive.StabilizerSylowConjugacy

end CFSG
