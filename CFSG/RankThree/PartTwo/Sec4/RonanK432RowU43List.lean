module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU43
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU43ListCen
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43
open CFSG.Assembly.RankThreeEven (projSU)

theorem witness_zS (hsyl : uSylCheck = true) :
    ∃ g : UX, (g * piU (sAt uZ) * g⁻¹) * piU (sAt uZ) = piU (sAt uZ) * (g * piU (sAt uZ) * g⁻¹) ∧
      g * piU (sAt uZ) * g⁻¹ ∉ Subgroup.zpowers (piU (sAt uZ)) := by
  have hX : piU (wordElem [1, 1, 1]) * piU (sAt uZ) * (piU (wordElem [1, 1, 1]))⁻¹ =
      piU u43X := by
    unfold u43X
    simp only [map_mul, map_inv]
  refine ⟨piU (wordElem [1, 1, 1]), ?_, ?_⟩
  · rw [hX, ← map_mul, ← map_mul, u43X_comm hsyl]
  · rw [hX]
    intro hmem
    have hz3 : (piU (sAt uZ)) ^ 3 = 1 := by
      rw [← map_pow, sAt_uZ_pow_three hsyl, map_one]
    have hX3 : u43X ^ 3 = 1 := by
      unfold u43X
      exact conj_pow_three_eq_one (sAt_uZ_pow_three hsyl) _
    rcases mem_zpowers_cases_of_pow_three hz3 hmem with h | h | h
    · exact u43X_ne_one hsyl (piU_injOn_order3 hX3 (one_pow 3) (by rw [h, map_one]))
    · exact u43X_ne_z hsyl (piU_injOn_order3 hX3 (sAt_uZ_pow_three hsyl) h)
    · exact u43X_ne_inv hsyl (piU_injOn_order3 hX3
        (by rw [inv_pow, sAt_uZ_pow_three hsyl, inv_one]) (by rw [h, map_inv]))

theorem witness_inv {v : UX} (h : ∃ g : UX, Commute (g * v * g⁻¹) v ∧
    g * v * g⁻¹ ∉ Subgroup.zpowers v) :
    ∃ g : UX, (g * v⁻¹ * g⁻¹) * v⁻¹ = v⁻¹ * (g * v⁻¹ * g⁻¹) ∧
      g * v⁻¹ * g⁻¹ ∉ Subgroup.zpowers v⁻¹ := by
  obtain ⟨g, hc, hn⟩ := h
  have e : g * v⁻¹ * g⁻¹ = (g * v * g⁻¹)⁻¹ := by group
  refine ⟨g, ?_, ?_⟩
  · rw [e]
    exact hc.inv_inv
  · rw [e, Subgroup.zpowers_inv]
    intro h'
    apply hn
    have h'' := Subgroup.inv_mem _ h'
    rwa [inv_inv] at h''

theorem hw_sylX (hsyl : uSylCheck = true) :
    ∀ u ∈ sylX, orderOf u = 3 → (∀ q ∈ sylX, q * u = u * q) →
      ∃ g : UX, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  intro u hu huo hcomm
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hu
  have hcen : ∀ g ∈ sylS, g * s = s * g := by
    intro g hg
    apply piU_injOn_sylS hsyl (sylS.mul_mem hg hs) (sylS.mul_mem hs hg)
    rw [map_mul, map_mul]
    exact hcomm (piU g) (Subgroup.mem_map_of_mem piU hg)
  rcases centre_sylS hsyl hs hcen with h | h | h
  · rw [h, map_one, orderOf_one] at huo
    exact absurd huo (by norm_num)
  · rw [h]
    exact witness_zS hsyl
  · rw [h, map_inv]
    exact witness_inv (witness_zS hsyl)

theorem listRow_UX : ListRow UX :=
  listRow_of_sylow_center 6 sylX
    (by rw [card_sylX uSylCheck_true, card_UX, factorization_three_card_UX])
    (by rw [card_UX]; norm_num)
    (hw_sylX uSylCheck_true)

theorem listRow_u43 : ListRow (projSU 4 3 1) :=
  haveI : Finite (projSU 4 3 1) := Finite.of_equiv UX projSUEquivUX.symm.toEquiv
  ListRow.of_mulEquiv projSUEquivUX.symm listRow_UX

theorem row_u43 : RowOf (projSU 4 3 1) :=
  haveI : Finite (projSU 4 3 1) := Finite.of_equiv UX projSUEquivUX.symm.toEquiv
  row_u43_of_listRow listRow_u43

end CFSG.RankThree.PartTwo.Sec4.RonanK432
