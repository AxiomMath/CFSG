module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.W18Five
public import CFSG.LocalAnalysis.WeakClosure81.W18Shape
public import CFSG.LocalAnalysis.WeakClosure81.EightTenAux

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem calNIn_eq_of_AS {H T : Subgroup G} {P : ∀ (X : Type) [Group X], Prop}
    {M : Subgroup G} (hN : calNIn H T = {lGen P H T}) (hle : lGen P H T ≤ H ⊓ M)
    (hTM : T ≤ H ⊓ M) (hlt : H ⊓ M < H) : calNIn H T = {H ⊓ M} := by
  obtain ⟨X, hX, hMX⟩ := exists_mem_calNIn_of_lt hTM hlt
  rw [hN, Set.mem_singleton_iff] at hX
  subst hX
  rw [hN, le_antisymm hle hMX]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem calNIn_eq_AS (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (h : MinCex183 D V₀ V H i) :
    calNIn H D.T = {H ⊓ D.M} := by
  obtain ⟨hTM, hlt⟩ := inf_lt h
  rcases not_and_or.mp h.fail with h1 | h2
  · obtain ⟨hK, hT, hTlt, h3, hno, hne⟩ := h.hyps_5_13 h1
    exact calNIn_eq_of_AS (h5_13 G H D.T hK hT hTlt h3 hno hne).1 (h.lGen_one_le_inf h1) hTM hlt
  · obtain ⟨hK, hT, hTlt, hno, hne, hp⟩ := h.hyps_5_11 h2
    exact calNIn_eq_of_AS (h5_11 G H D.T hK hT hTlt hno hne hp).1.1 (h.lGen_zero_le_inf h2) hTM
      hlt

theorem not_shape512Four_AS (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) :
    ¬ Shape512Four H :=
  not_shape512Four_of_calNIn c.hyp.isSylowIn_T D.sylowM.le c.hyp.notLe
    (c.calNIn_eq_AS h5_11 h5_13) (not_concl181_iff.mp h1).1.2

theorem oInf_eq_kerMV_of_component_AS (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (c : MinCex183 D V₀ V H i) {L : Subgroup G} (hL : IsComponentModN (OInf H) H L)
    (hLT : L ⊔ D.T = H) : OInf H = kerMV V H :=
  CFSG.LocalAnalysis.WeakClosure81.oInf_eq_kerMV c.hyp.isSylowIn_T
    (by rw [c.hyp.setting.normalizer_eq]; exact c.calNIn_eq_AS h5_11 h5_13) ⟨L, hL, hLT⟩

theorem exists_component182_ker_AS (h172 : W3Thm172Weak G) (h5_4 : Asch5_4) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i) :
    OInf H = kerMV V H ∧ ∃ L : Subgroup G, IsComponentModN (kerMV V H) H L ∧ L ⊔ D.T = H ∧
      Shape54 H D.T L := by
  obtain ⟨L, hL, hLT, hshape⟩ := c.exists_component182 h172 h5_4 h2
  have hK := c.oInf_eq_kerMV_of_component_AS h5_11 h5_13 hL hLT
  exact ⟨hK, L, hK ▸ hL, hLT, hshape⟩

theorem exists_shape185_AS (h172 : W3Thm172Weak G) (h5_12 : Asch5_12)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i)
    (h1 : ¬ Concl181 D V₀ V H) :
    IsSolvable ↥(relPPrimeCore 3 H) ∧ kerMV V H = relPPrimeCore 3 H ∧ Shape185 H := by
  obtain ⟨hsolv, hQM, hshape⟩ := c.exists_shape512 h172 h5_12 h1
  have hsp := (not_concl181_iff.mp h1).1.2
  exact ⟨hsolv, c.kerMV_eq_relPPrimeCore hsp (hQM.trans inf_le_right), hshape,
    c.not_shape512Four_AS h5_11 h5_13 h1⟩

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
