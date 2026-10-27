module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Three
public import CFSG.RankThree.GF2n.Stroth78.Sec2Conj

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem mem_centerIn_QaOf_of_isConj (S : Setting z E F) {a : G} (hconj : IsConj z a) :
    a ∈ centerIn (QaOf a) := by
  obtain ⟨c, hc⟩ := hconj
  have hcz : (c : G) * z = a * (c : G) := hc.eq
  have ha_eq : a = (c : G) * z * (c : G)⁻¹ := by
    calc
      a = a * (c : G) * (c : G)⁻¹ := by group
      _ = (c : G) * z * (c : G)⁻¹ := by rw [← hcz]
  have hQa_eq : QaOf a = (Q z).map (MulAut.conj (c : G)).toMonoidHom := by
    show fStar (Subgroup.centralizer ({a} : Set G)) =
      (fStar (Subgroup.centralizer ({z} : Set G))).map
        (MulAut.conj (c : G)).toMonoidHom
    rw [ha_eq, centralizer_map_conj z (c : G), fStar_map_conj]
  have hzcent : z ∈ Subgroup.centralizer (Q z : Set G) :=
    (Subgroup.mem_inf.mp (z_mem_ZQ S)).2
  have haQa : a ∈ QaOf a := mem_QaOf_self a
  have haCent : a ∈ Subgroup.centralizer (QaOf a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hQa_eq] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hzy : z * y = y * z := (Subgroup.mem_centralizer_iff.mp hzcent y hy).symm
    calc
      ((c : G) * y * (c : G)⁻¹) * a =
          ((c : G) * y * (c : G)⁻¹) * ((c : G) * z * (c : G)⁻¹) := by rw [ha_eq]
      _ = (c : G) * (y * z) * (c : G)⁻¹ := by group
      _ = (c : G) * (z * y) * (c : G)⁻¹ := by rw [hzy.symm]
      _ = ((c : G) * z * (c : G)⁻¹) * ((c : G) * y * (c : G)⁻¹) := by group
      _ = a * ((c : G) * y * (c : G)⁻¹) := by rw [ha_eq]
  exact Subgroup.mem_inf.mpr ⟨haQa, haCent⟩

end CFSG.RankThree.GF2n.Stroth78
