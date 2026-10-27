module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem isHStar_of_uFamHat_of_max_le {T Mc M X P : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hXMc : X ≤ Mc) (hTMc : T ≤ Mc) (hMc : pCoreOf 2 Mc ≠ ⊥) (hP : P ∈ uFamHat X T)
    (hPM : ¬ P ≤ M)
    (hmax : ∀ N : Subgroup G, IsMaxSubgroupIn P N → T ≤ N → N ≤ M) : IsHStar T M P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hPX, hTP, -⟩, -⟩ := hP
  let S : Sylow 2 G := hT.1.toSylow hT.2
  have hInH : InH T P := inH_of_le S (Y := P) (H := Mc) hTP.le (hPX.trans hXMc) ⟨hTMc, hMc⟩
  refine ⟨hInH, hPM, ?_⟩
  intro Y hY hYP hYM
  by_contra hne
  have hlt : Y < P := lt_of_le_of_ne hYP hne
  obtain ⟨N, ⟨hYN, hNP⟩, hNmax⟩ := (wellFounded_gt (α := Subgroup G)).has_min
    {K : Subgroup G | Y ≤ K ∧ K < P} ⟨Y, le_rfl, hlt⟩
  have hNM : IsMaxSubgroupIn P N := by
    refine ⟨hNP, fun K hK hKP => ?_⟩
    by_contra hKne
    exact hNmax K ⟨hYN.trans hK.le, lt_of_le_of_ne hKP hKne⟩ hK
  exact hYM ((hYN.trans (hmax N hNM (hY.1.trans hYN))))

omit [Finite G] in
theorem le_Mc_of_case {T Mc Kc : Subgroup G} (hTMc : T ≤ Mc)
    (h : Case15212ii T Mc Kc ∨ Case15212iii T Mc Kc) : Kc ≤ Mc := by
  rcases h with h | ⟨L, t, -, hL, htT, -, hKc, -, -⟩
  · exact le_of_mem_cComp h.2.1
  · rw [hKc]
    refine sup_le (le_of_mem_cComp hL) ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hx
    exact Mc.mul_mem (Mc.mul_mem (hTMc htT) (le_of_mem_cComp hL hl)) (Mc.inv_mem (hTMc htT))

end CFSG.Quasithin
