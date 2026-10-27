module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCOdd
public import CFSG.LocalAnalysis.UniquenessCase.UC6Close

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_oddNcCore_of_case168_11 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (h : Case168_11 D V₀ V hV L) :
    OddNcCore D V₀ V hV := by
  obtain ⟨hcyc, -, hs, hsig⟩ := h
  have h7σ : 7 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 7
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hLp : IsPGroup 7 ↥(lBar V₀ V hV L) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hcyc.2)
  have hL1 : lBar V₀ V hV L ≠ ⊥ := by
    intro hb
    have := hcyc.2
    rw [hb, Subgroup.card_bot] at this
    omega
  have hLle : lBar V₀ V hV L ≤ pCoreOf 7 (Mbar D.M V₀ V hV) :=
    s16c13bc_lBar_le_pCoreOf D hV hc (by norm_num) hLp hL1
  have hs' : Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := hs
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.1 hs'
  have hxmem : x ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := by
    rw [hset]
    exact Set.mem_insert _ _
  have hymem : y ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := by
    rw [hset]
    exact Set.mem_insert_of_mem _ rfl
  have hnorm : (pCore 7 ↥(Mbar D.M V₀ V hV)).Normal := CFSG.pCore_normal
  have hcore : ∀ Z ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom},
      Z ≤ pCoreOf 7 (Mbar D.M V₀ V hV) ∧ Nat.card ↥Z = 7 := by
    rintro Z ⟨φ, hφ, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 (hLle ha)
      exact ⟨⟨φ, hφ⟩ * b * ⟨φ, hφ⟩⁻¹, hnorm.conj_mem b hb ⟨φ, hφ⟩, rfl⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj φ).injective]
      exact hcyc.2
  have hpg : IsPGroup 7 ↥(pCoreOf 7 (Mbar D.M V₀ V hV)) :=
    (CFSG.pCore_isPGroup (p := 7) (G := ↥(Mbar D.M V₀ V hV))).map (Mbar D.M V₀ V hV).subtype
  refine s16c13bc_oddNcCore_of_le_pCoreOf D hV h7σ le_rfl hpg ?_
  intro hcycl
  exact hxy (UC6.eq_of_card_eq_of_isCyclic hcycl (hcore x hxmem).1 (hcore y hymem).1
    ((hcore x hxmem).2.trans (hcore y hymem).2.symm))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
